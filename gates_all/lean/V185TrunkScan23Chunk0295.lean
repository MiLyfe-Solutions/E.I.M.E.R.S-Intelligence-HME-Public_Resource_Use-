import V185TrunkScan23Chunk0294

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1744559 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 3]
def baseStart_1744559 : Nat := 118140960795 + 1744559 * 2 ^ 59
def prefixEnd_1744559 : Nat := 4983230072969 + 3 ^ 40 * 1744559 * 2
def baseEnd_1744559 : Nat := 895797297127145138589425

theorem tailTrace_1744559 : CollatzResearch.WordTrace tailWord_1744559 prefixEnd_1744559 895797297127145138589425 := by
  unfold tailWord_1744559
  simp only [CollatzResearch.WordTrace]
  refine ⟨63629294086768164801540731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42419529391178776534360487 63629294086768164801540731)
  ·
    refine ⟨95443941130152247202311097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63629294086768164801540731 95443941130152247202311097)
    ·
      refine ⟨71582955847614185401733323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95443941130152247202311097 71582955847614185401733323)
      ·
        refine ⟨107374433771421278102599985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71582955847614185401733323 107374433771421278102599985)
        ·
          refine ⟨80530825328565958576949989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107374433771421278102599985 80530825328565958576949989)
          ·
            refine ⟨15099529749106117233178123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80530825328565958576949989 15099529749106117233178123)
            ·
              refine ⟨22649294623659175849767185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15099529749106117233178123 22649294623659175849767185)
              ·
                refine ⟨16986970967744381887325389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22649294623659175849767185 16986970967744381887325389)
                ·
                  refine ⟨6370114112904143207747021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16986970967744381887325389 6370114112904143207747021)
                  ·
                    refine ⟨2388792792339053702905133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6370114112904143207747021 2388792792339053702905133)
                    ·
                      refine ⟨895797297127145138589425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2388792792339053702905133 895797297127145138589425)
                      ·
                        rfl

theorem cell23_1744559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_1744559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744559 prefixEnd_1744559 := by exact prefixLift 1744559
  have htrace : WordTrace (prefixWord ++ tailWord_1744559) baseStart_1744559 baseEnd_1744559 := by
    simpa [prefixWord, tailWord_1744559, baseEnd_1744559] using wordTrace_append hprefix tailTrace_1744559
  have hstable : (prefixWord ++ tailWord_1744559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744559).length < 2 ^ (prefixWord ++ tailWord_1744559).sum := by decide
  have hdescent : baseEnd_1744559 < baseStart_1744559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744576 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3]
def baseStart_1744576 : Nat := 118140960795 + 1744576 * 2 ^ 59
def prefixEnd_1744576 : Nat := 4983230072969 + 3 ^ 40 * 1744576 * 2
def baseEnd_1744576 : Nat := 895806026298271572076847

theorem tailTrace_1744576 : CollatzResearch.WordTrace tailWord_1744576 prefixEnd_1744576 895806026298271572076847 := by
  unfold tailWord_1744576
  simp only [CollatzResearch.WordTrace]
  refine ⟨31814957063853288352454791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42419942751804384469939721 31814957063853288352454791)
  ·
    refine ⟨47722435595779932528682187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31814957063853288352454791 47722435595779932528682187)
    ·
      refine ⟨71583653393669898793023281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47722435595779932528682187 71583653393669898793023281)
      ·
        refine ⟨53687740045252424094767461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71583653393669898793023281 53687740045252424094767461)
        ·
          refine ⟨10066451258484829517768899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53687740045252424094767461 10066451258484829517768899)
          ·
            refine ⟨15099676887727244276653349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066451258484829517768899 15099676887727244276653349)
            ·
              refine ⟨2831189416448858301872503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15099676887727244276653349 2831189416448858301872503)
              ·
                refine ⟨4246784124673287452808755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831189416448858301872503 4246784124673287452808755)
                ·
                  refine ⟨6370176187009931179213133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246784124673287452808755 6370176187009931179213133)
                  ·
                    refine ⟨2388816070128724192204925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6370176187009931179213133 2388816070128724192204925)
                    ·
                      refine ⟨895806026298271572076847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2388816070128724192204925 895806026298271572076847)
                      ·
                        rfl

theorem cell23_1744576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_1744576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744576 prefixEnd_1744576 := by exact prefixLift 1744576
  have htrace : WordTrace (prefixWord ++ tailWord_1744576) baseStart_1744576 baseEnd_1744576 := by
    simpa [prefixWord, tailWord_1744576, baseEnd_1744576] using wordTrace_append hprefix tailTrace_1744576
  have hstable : (prefixWord ++ tailWord_1744576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744576).length < 2 ^ (prefixWord ++ tailWord_1744576).sum := by decide
  have hdescent : baseEnd_1744576 < baseStart_1744576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744619 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 3]
def baseStart_1744619 : Nat := 118140960795 + 1744619 * 2 ^ 59
def prefixEnd_1744619 : Nat := 4983230072969 + 3 ^ 40 * 1744619 * 2
def baseEnd_1744619 : Nat := 895828105966414903839149

theorem tailTrace_1744619 : CollatzResearch.WordTrace tailWord_1744619 prefixEnd_1744619 895828105966414903839149 := by
  unfold tailWord_1744619
  simp only [CollatzResearch.WordTrace]
  refine ⟨63631482466550795048724911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42420988311033863365816607 63631482466550795048724911)
  ·
    refine ⟨95447223699826192573087367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63631482466550795048724911 95447223699826192573087367)
    ·
      refine ⟨143170835549739288859631051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95447223699826192573087367 143170835549739288859631051)
      ·
        refine ⟨214756253324608933289446577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143170835549739288859631051 214756253324608933289446577)
        ·
          refine ⟨161067189993456699967084933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214756253324608933289446577 161067189993456699967084933)
          ·
            refine ⟨30200098123773131243828425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161067189993456699967084933 30200098123773131243828425)
            ·
              refine ⟨22650073592829848432871319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30200098123773131243828425 22650073592829848432871319)
              ·
                refine ⟨33975110389244772649306979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22650073592829848432871319 33975110389244772649306979)
                ·
                  refine ⟨50962665583867158973960469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33975110389244772649306979 50962665583867158973960469)
                  ·
                    refine ⟨2388874949243773076904397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50962665583867158973960469 2388874949243773076904397)
                    ·
                      refine ⟨895828105966414903839149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2388874949243773076904397 895828105966414903839149)
                      ·
                        rfl

theorem cell23_1744619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 3].length) (baseStart_1744619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744619 prefixEnd_1744619 := by exact prefixLift 1744619
  have htrace : WordTrace (prefixWord ++ tailWord_1744619) baseStart_1744619 baseEnd_1744619 := by
    simpa [prefixWord, tailWord_1744619, baseEnd_1744619] using wordTrace_append hprefix tailTrace_1744619
  have hstable : (prefixWord ++ tailWord_1744619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744619).length < 2 ^ (prefixWord ++ tailWord_1744619).sum := by decide
  have hdescent : baseEnd_1744619 < baseStart_1744619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744639 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 7]
def baseStart_1744639 : Nat := 118140960795 + 1744639 * 2 ^ 59
def prefixEnd_1744639 : Nat := 4983230072969 + 3 ^ 40 * 1744639 * 2
def baseEnd_1744639 : Nat := 99537597286611647287673

theorem tailTrace_1744639 : CollatzResearch.WordTrace tailWord_1744639 prefixEnd_1744639 99537597286611647287673 := by
  unfold tailWord_1744639
  simp only [CollatzResearch.WordTrace]
  refine ⟨63632211926478338464452971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42421474617652225642968647 63632211926478338464452971)
  ·
    refine ⟨95448317889717507696679457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63632211926478338464452971 95448317889717507696679457)
    ·
      refine ⟨71586238417288130772509593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95448317889717507696679457 71586238417288130772509593)
      ·
        refine ⟨53689678812966098079382195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71586238417288130772509593 53689678812966098079382195)
        ·
          refine ⟨80534518219449147119073293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53689678812966098079382195 80534518219449147119073293)
          ·
            refine ⟨30200444332293430169652485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80534518219449147119073293 30200444332293430169652485)
            ·
              refine ⟨5662583312305018156809841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30200444332293430169652485 5662583312305018156809841)
              ·
                refine ⟨4246937484228763617607381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662583312305018156809841 4246937484228763617607381)
                ·
                  refine ⟨99537597286611647287673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4246937484228763617607381 99537597286611647287673)
                  ·
                    rfl

theorem cell23_1744639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 7].length) (baseStart_1744639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744639 prefixEnd_1744639 := by exact prefixLift 1744639
  have htrace : WordTrace (prefixWord ++ tailWord_1744639) baseStart_1744639 baseEnd_1744639 := by
    simpa [prefixWord, tailWord_1744639, baseEnd_1744639] using wordTrace_append hprefix tailTrace_1744639
  have hstable : (prefixWord ++ tailWord_1744639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744639).length < 2 ^ (prefixWord ++ tailWord_1744639).sum := by decide
  have hdescent : baseEnd_1744639 < baseStart_1744639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744703 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 2, 5]
def baseStart_1744703 : Nat := 118140960795 + 1744703 * 2 ^ 59
def prefixEnd_1744703 : Nat := 4983230072969 + 3 ^ 40 * 1744703 * 2
def baseEnd_1744703 : Nat := 298623746113797525062921

theorem tailTrace_1744703 : CollatzResearch.WordTrace tailWord_1744703 prefixEnd_1744703 298623746113797525062921 := by
  unfold tailWord_1744703
  simp only [CollatzResearch.WordTrace]
  refine ⟨63634546198246477394782763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42423030798830984929855175 63634546198246477394782763)
  ·
    refine ⟨95451819297369716092174145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63634546198246477394782763 95451819297369716092174145)
    ·
      refine ⟨71588864473027287069130609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95451819297369716092174145 71588864473027287069130609)
      ·
        refine ⟨53691648354770465301847957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71588864473027287069130609 53691648354770465301847957)
        ·
          refine ⟨2516796016629865561024123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53691648354770465301847957 2516796016629865561024123)
          ·
            refine ⟨3775194024944798341536185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516796016629865561024123 3775194024944798341536185)
            ·
              refine ⟨2831395518708598756152139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3775194024944798341536185 2831395518708598756152139)
              ·
                refine ⟨4247093278062898134228209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831395518708598756152139 4247093278062898134228209)
                ·
                  refine ⟨3185319958547173600671157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4247093278062898134228209 3185319958547173600671157)
                  ·
                    refine ⟨298623746113797525062921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3185319958547173600671157 298623746113797525062921)
                    ·
                      rfl

theorem cell23_1744703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_1744703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744703 prefixEnd_1744703 := by exact prefixLift 1744703
  have htrace : WordTrace (prefixWord ++ tailWord_1744703) baseStart_1744703 baseEnd_1744703 := by
    simpa [prefixWord, tailWord_1744703, baseEnd_1744703] using wordTrace_append hprefix tailTrace_1744703
  have hstable : (prefixWord ++ tailWord_1744703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744703).length < 2 ^ (prefixWord ++ tailWord_1744703).sum := by decide
  have hdescent : baseEnd_1744703 < baseStart_1744703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744740 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_1744740 : Nat := 118140960795 + 1744740 * 2 ^ 59
def prefixEnd_1744740 : Nat := 4983230072969 + 3 ^ 40 * 1744740 * 2
def baseEnd_1744740 : Nat := 895890237125608930426093

theorem tailTrace_1744740 : CollatzResearch.WordTrace tailWord_1744740 prefixEnd_1744740 895890237125608930426093 := by
  unfold tailWord_1744740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31817947849556216356939837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42423930466074955142586449 31817947849556216356939837)
  ·
    refine ⟨11931730443583581133852439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31817947849556216356939837 11931730443583581133852439)
    ·
      refine ⟨17897595665375371700778659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11931730443583581133852439 17897595665375371700778659)
      ·
        refine ⟨26846393498063057551167989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17897595665375371700778659 26846393498063057551167989)
        ·
          refine ⟨2516849390443411645421999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26846393498063057551167989 2516849390443411645421999)
          ·
            refine ⟨3775274085665117468132999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516849390443411645421999 3775274085665117468132999)
            ·
              refine ⟨5662911128497676202199499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775274085665117468132999 5662911128497676202199499)
              ·
                refine ⟨8494366692746514303299249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662911128497676202199499 8494366692746514303299249)
                ·
                  refine ⟨6370775019559885727474437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8494366692746514303299249 6370775019559885727474437)
                  ·
                    refine ⟨1194520316167478573901457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6370775019559885727474437 1194520316167478573901457)
                    ·
                      refine ⟨895890237125608930426093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194520316167478573901457 895890237125608930426093)
                      ·
                        rfl

theorem cell23_1744740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_1744740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744740 prefixEnd_1744740 := by exact prefixLift 1744740
  have htrace : WordTrace (prefixWord ++ tailWord_1744740) baseStart_1744740 baseEnd_1744740 := by
    simpa [prefixWord, tailWord_1744740, baseEnd_1744740] using wordTrace_append hprefix tailTrace_1744740
  have hstable : (prefixWord ++ tailWord_1744740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744740).length < 2 ^ (prefixWord ++ tailWord_1744740).sum := by decide
  have hdescent : baseEnd_1744740 < baseStart_1744740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744750 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1744750 : Nat := 118140960795 + 1744750 * 2 ^ 59
def prefixEnd_1744750 : Nat := 4983230072969 + 3 ^ 40 * 1744750 * 2
def baseEnd_1744750 : Nat := 298631790644051297100349

theorem tailTrace_1744750 : CollatzResearch.WordTrace tailWord_1744750 prefixEnd_1744750 298631790644051297100349 := by
  unfold tailWord_1744750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954532553634525552717963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42424173619384136281162469 7954532553634525552717963)
  ·
    refine ⟨11931798830451788329076945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7954532553634525552717963 11931798830451788329076945)
    ·
      refine ⟨8948849122838841246807709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11931798830451788329076945 8948849122838841246807709)
      ·
        refine ⟨3355818421064565467552891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8948849122838841246807709 3355818421064565467552891)
        ·
          refine ⟨5033727631596848201329337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3355818421064565467552891 5033727631596848201329337)
          ·
            refine ⟨3775295723697636150997003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5033727631596848201329337 3775295723697636150997003)
            ·
              refine ⟨5662943585546454226495505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775295723697636150997003 5662943585546454226495505)
              ·
                refine ⟨4247207689159840669871629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662943585546454226495505 4247207689159840669871629)
                ·
                  refine ⟨1592702883434940251201861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4247207689159840669871629 1592702883434940251201861)
                  ·
                    refine ⟨298631790644051297100349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1592702883434940251201861 298631790644051297100349)
                    ·
                      rfl

theorem cell23_1744750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1744750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744750 prefixEnd_1744750 := by exact prefixLift 1744750
  have htrace : WordTrace (prefixWord ++ tailWord_1744750) baseStart_1744750 baseEnd_1744750 := by
    simpa [prefixWord, tailWord_1744750, baseEnd_1744750] using wordTrace_append hprefix tailTrace_1744750
  have hstable : (prefixWord ++ tailWord_1744750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744750).length < 2 ^ (prefixWord ++ tailWord_1744750).sum := by decide
  have hdescent : baseEnd_1744750 < baseStart_1744750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744773 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_1744773 : Nat := 118140960795 + 1744773 * 2 ^ 59
def prefixEnd_1744773 : Nat := 4983230072969 + 3 ^ 40 * 1744773 * 2
def baseEnd_1744773 : Nat := 895907181987207301313441

theorem tailTrace_1744773 : CollatzResearch.WordTrace tailWord_1744773 prefixEnd_1744773 895907181987207301313441 := by
  unfold tailWord_1744773
  simp only [CollatzResearch.WordTrace]
  refine ⟨63637099307992879349830973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42424732871995252899887315 63637099307992879349830973)
  ·
    refine ⟨23863912240497329756186615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63637099307992879349830973 23863912240497329756186615)
    ·
      refine ⟨35795868360745994634279923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23863912240497329756186615 35795868360745994634279923)
      ·
        refine ⟨53693802541118991951419885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35795868360745994634279923 53693802541118991951419885)
        ·
          refine ⟨20135175952919621981782457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53693802541118991951419885 20135175952919621981782457)
          ·
            refine ⟨15101381964689716486336843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20135175952919621981782457 15101381964689716486336843)
            ·
              refine ⟨22652072947034574729505265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15101381964689716486336843 22652072947034574729505265)
              ·
                refine ⟨16989054710275931047128949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22652072947034574729505265 16989054710275931047128949)
                ·
                  refine ⟨1592723879088368535668339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16989054710275931047128949 1592723879088368535668339)
                  ·
                    refine ⟨2389085818632552803502509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1592723879088368535668339 2389085818632552803502509)
                    ·
                      refine ⟨895907181987207301313441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389085818632552803502509 895907181987207301313441)
                      ·
                        rfl

theorem cell23_1744773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_1744773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744773 prefixEnd_1744773 := by exact prefixLift 1744773
  have htrace : WordTrace (prefixWord ++ tailWord_1744773) baseStart_1744773 baseEnd_1744773 := by
    simpa [prefixWord, tailWord_1744773, baseEnd_1744773] using wordTrace_append hprefix tailTrace_1744773
  have hstable : (prefixWord ++ tailWord_1744773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744773).length < 2 ^ (prefixWord ++ tailWord_1744773).sum := by decide
  have hdescent : baseEnd_1744773 < baseStart_1744773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744816 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3]
def baseStart_1744816 : Nat := 118140960795 + 1744816 * 2 ^ 59
def prefixEnd_1744816 : Nat := 4983230072969 + 3 ^ 40 * 1744816 * 2
def baseEnd_1744816 : Nat := 895929261655350633075743

theorem tailTrace_1744816 : CollatzResearch.WordTrace tailWord_1744816 prefixEnd_1744816 895929261655350633075743 := by
  unfold tailWord_1744816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31819333823418548846823151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42425778431224731795764201 31819333823418548846823151)
  ·
    refine ⟨47729000735127823270234727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31819333823418548846823151 47729000735127823270234727)
    ·
      refine ⟨71593501102691734905352091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47729000735127823270234727 71593501102691734905352091)
      ·
        refine ⟨107390251654037602358028137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71593501102691734905352091 107390251654037602358028137)
        ·
          refine ⟨80542688740528201768521103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107390251654037602358028137 80542688740528201768521103)
          ·
            refine ⟨120814033110792302652781655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80542688740528201768521103 120814033110792302652781655)
            ·
              refine ⟨181221049666188453979172483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120814033110792302652781655 181221049666188453979172483)
              ·
                refine ⟨271831574499282680968758725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181221049666188453979172483 271831574499282680968758725)
                ·
                  refine ⟨50968420218615502681642261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271831574499282680968758725 50968420218615502681642261)
                  ·
                    refine ⟨2389144697747601688201981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50968420218615502681642261 2389144697747601688201981)
                    ·
                      refine ⟨895929261655350633075743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389144697747601688201981 895929261655350633075743)
                      ·
                        rfl

theorem cell23_1744816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_1744816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744816 prefixEnd_1744816 := by exact prefixLift 1744816
  have htrace : WordTrace (prefixWord ++ tailWord_1744816) baseStart_1744816 baseEnd_1744816 := by
    simpa [prefixWord, tailWord_1744816, baseEnd_1744816] using wordTrace_append hprefix tailTrace_1744816
  have hstable : (prefixWord ++ tailWord_1744816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744816).length < 2 ^ (prefixWord ++ tailWord_1744816).sum := by decide
  have hdescent : baseEnd_1744816 < baseStart_1744816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744830 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1744830 : Nat := 118140960795 + 1744830 * 2 ^ 59
def prefixEnd_1744830 : Nat := 4983230072969 + 3 ^ 40 * 1744830 * 2
def baseEnd_1744830 : Nat := 895936450384513578300679

theorem tailTrace_1744830 : CollatzResearch.WordTrace tailWord_1744830 prefixEnd_1744830 895936450384513578300679 := by
  unfold tailWord_1744830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954897283598297260581993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42426118845857585389770629 7954897283598297260581993)
  ·
    refine ⟨5966172962698722945436495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7954897283598297260581993 5966172962698722945436495)
    ·
      refine ⟨8949259444048084418154743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5966172962698722945436495 8949259444048084418154743)
      ·
        refine ⟨13423889166072126627232115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8949259444048084418154743 13423889166072126627232115)
        ·
          refine ⟨20135833749108189940848173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13423889166072126627232115 20135833749108189940848173)
          ·
            refine ⟨7550937655915571227818065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20135833749108189940848173 7550937655915571227818065)
            ·
              refine ⟨5663203241936678420863549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7550937655915571227818065 5663203241936678420863549)
              ·
                refine ⟨2123701215726254407823831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5663203241936678420863549 2123701215726254407823831)
                ·
                  refine ⟨3185551823589381611735747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123701215726254407823831 3185551823589381611735747)
                  ·
                    refine ⟨4778327735384072417603621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3185551823589381611735747 4778327735384072417603621)
                    ·
                      refine ⟨895936450384513578300679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4778327735384072417603621 895936450384513578300679)
                      ·
                        rfl

theorem cell23_1744830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1744830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744830 prefixEnd_1744830 := by exact prefixLift 1744830
  have htrace : WordTrace (prefixWord ++ tailWord_1744830) baseStart_1744830 baseEnd_1744830 := by
    simpa [prefixWord, tailWord_1744830, baseEnd_1744830] using wordTrace_append hprefix tailTrace_1744830
  have hstable : (prefixWord ++ tailWord_1744830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744830).length < 2 ^ (prefixWord ++ tailWord_1744830).sum := by decide
  have hdescent : baseEnd_1744830 < baseStart_1744830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744853 : List Nat := [1, 3, 2, 3, 2, 2, 2, 8]
def baseStart_1744853 : Nat := 118140960795 + 1744853 * 2 ^ 59
def prefixEnd_1744853 : Nat := 4983230072969 + 3 ^ 40 * 1744853 * 2
def baseEnd_1744853 : Nat := 33183268905169147715299

theorem tailTrace_1744853 : CollatzResearch.WordTrace tailWord_1744853 prefixEnd_1744853 33183268905169147715299 := by
  unfold tailWord_1744853
  simp only [CollatzResearch.WordTrace]
  refine ⟨63640017147703053012743213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42426678098468702008495475 63640017147703053012743213)
  ·
    refine ⟨23865006430388644879778705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63640017147703053012743213 23865006430388644879778705)
    ·
      refine ⟨17898754822791483659834029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23865006430388644879778705 17898754822791483659834029)
      ·
        refine ⟨6712033058546806372437761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17898754822791483659834029 6712033058546806372437761)
        ·
          refine ⟨5034024793910104779328321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6712033058546806372437761 5034024793910104779328321)
          ·
            refine ⟨3775518595432578584496241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5034024793910104779328321 3775518595432578584496241)
            ·
              refine ⟨2831638946574433938372181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3775518595432578584496241 2831638946574433938372181)
              ·
                refine ⟨33183268905169147715299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2831638946574433938372181 33183268905169147715299)
                ·
                  rfl

theorem cell23_1744853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 8].length) (baseStart_1744853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744853 prefixEnd_1744853 := by exact prefixLift 1744853
  have htrace : WordTrace (prefixWord ++ tailWord_1744853) baseStart_1744853 baseEnd_1744853 := by
    simpa [prefixWord, tailWord_1744853, baseEnd_1744853] using wordTrace_append hprefix tailTrace_1744853
  have hstable : (prefixWord ++ tailWord_1744853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744853).length < 2 ^ (prefixWord ++ tailWord_1744853).sum := by decide
  have hdescent : baseEnd_1744853 < baseStart_1744853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744856 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1744856 : Nat := 118140960795 + 1744856 * 2 ^ 59
def prefixEnd_1744856 : Nat := 4983230072969 + 3 ^ 40 * 1744856 * 2
def baseEnd_1744856 : Nat := 895949800881530476575559

theorem tailTrace_1744856 : CollatzResearch.WordTrace tailWord_1744856 prefixEnd_1744856 895949800881530476575559 := by
  unfold tailWord_1744856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31820063283346092262551211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42426751044461456350068281 31820063283346092262551211)
  ·
    refine ⟨47730094925019138393826817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31820063283346092262551211 47730094925019138393826817)
    ·
      refine ⟨35797571193764353795370113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47730094925019138393826817 35797571193764353795370113)
      ·
        refine ⟨26848178395323265346527585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35797571193764353795370113 26848178395323265346527585)
        ·
          refine ⟨20136133796492449009895689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26848178395323265346527585 20136133796492449009895689)
          ·
            refine ⟨15102100347369336757421767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20136133796492449009895689 15102100347369336757421767)
            ·
              refine ⟨22653150521054005136132651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15102100347369336757421767 22653150521054005136132651)
              ·
                refine ⟨33979725781581007704198977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22653150521054005136132651 33979725781581007704198977)
                ·
                  refine ⟨25484794336185755778149233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33979725781581007704198977 25484794336185755778149233)
                  ·
                    refine ⟨19113595752139316833611925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25484794336185755778149233 19113595752139316833611925)
                    ·
                      refine ⟨895949800881530476575559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19113595752139316833611925 895949800881530476575559)
                      ·
                        rfl

theorem cell23_1744856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1744856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744856 prefixEnd_1744856 := by exact prefixLift 1744856
  have htrace : WordTrace (prefixWord ++ tailWord_1744856) baseStart_1744856 baseEnd_1744856 := by
    simpa [prefixWord, tailWord_1744856, baseEnd_1744856] using wordTrace_append hprefix tailTrace_1744856
  have hstable : (prefixWord ++ tailWord_1744856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744856).length < 2 ^ (prefixWord ++ tailWord_1744856).sum := by decide
  have hdescent : baseEnd_1744856 < baseStart_1744856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744867 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1744867 : Nat := 118140960795 + 1744867 * 2 ^ 59
def prefixEnd_1744867 : Nat := 4983230072969 + 3 ^ 40 * 1744867 * 2
def baseEnd_1744867 : Nat := 895955449168729933538009

theorem tailTrace_1744867 : CollatzResearch.WordTrace tailWord_1744867 prefixEnd_1744867 895955449168729933538009 := by
  unfold tailWord_1744867
  simp only [CollatzResearch.WordTrace]
  refine ⟨63640527769652333403752855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42427018513101555602501903 63640527769652333403752855)
  ·
    refine ⟨95460791654478500105629283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63640527769652333403752855 95460791654478500105629283)
    ·
      refine ⟨143191187481717750158443925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95460791654478500105629283 143191187481717750158443925)
      ·
        refine ⟨6712086913205519538677059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143191187481717750158443925 6712086913205519538677059)
        ·
          refine ⟨10068130369808279308015589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712086913205519538677059 10068130369808279308015589)
          ·
            refine ⟨1887774444339052370252923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10068130369808279308015589 1887774444339052370252923)
            ·
              refine ⟨2831661666508578555379385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887774444339052370252923 2831661666508578555379385)
              ·
                refine ⟨2123746249881433916534539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831661666508578555379385 2123746249881433916534539)
                ·
                  refine ⟨3185619374822150874801809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123746249881433916534539 3185619374822150874801809)
                  ·
                    refine ⟨2389214531116613156101357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3185619374822150874801809 2389214531116613156101357)
                    ·
                      refine ⟨895955449168729933538009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389214531116613156101357 895955449168729933538009)
                      ·
                        rfl

theorem cell23_1744867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1744867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744867 prefixEnd_1744867 := by exact prefixLift 1744867
  have htrace : WordTrace (prefixWord ++ tailWord_1744867) baseStart_1744867 baseEnd_1744867 := by
    simpa [prefixWord, tailWord_1744867, baseEnd_1744867] using wordTrace_append hprefix tailTrace_1744867
  have hstable : (prefixWord ++ tailWord_1744867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744867).length < 2 ^ (prefixWord ++ tailWord_1744867).sum := by decide
  have hdescent : baseEnd_1744867 < baseStart_1744867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744876 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1744876 : Nat := 118140960795 + 1744876 * 2 ^ 59
def prefixEnd_1744876 : Nat := 4983230072969 + 3 ^ 40 * 1744876 * 2
def baseEnd_1744876 : Nat := 895960070494620398325467

theorem tailTrace_1744876 : CollatzResearch.WordTrace tailWord_1744876 prefixEnd_1744876 895960070494620398325467 := by
  unfold tailWord_1744876
  simp only [CollatzResearch.WordTrace]
  refine ⟨31820428013309863970415241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42427237351079818627220321 31820428013309863970415241)
  ·
    refine ⟨23865321009982397977811431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31820428013309863970415241 23865321009982397977811431)
    ·
      refine ⟨35797981514973596966717147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23865321009982397977811431 35797981514973596966717147)
      ·
        refine ⟨53696972272460395450075721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35797981514973596966717147 53696972272460395450075721)
        ·
          refine ⟨40272729204345296587556791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53696972272460395450075721 40272729204345296587556791)
          ·
            refine ⟨60409093806517944881335187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40272729204345296587556791 60409093806517944881335187)
            ·
              refine ⟨90613640709776917322002781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60409093806517944881335187 90613640709776917322002781)
              ·
                refine ⟨33980115266166343995751043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90613640709776917322002781 33980115266166343995751043)
                ·
                  refine ⟨50970172899249515993626565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33980115266166343995751043 50970172899249515993626565)
                  ·
                    refine ⟨9556907418609284248804981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50970172899249515993626565 9556907418609284248804981)
                    ·
                      refine ⟨895960070494620398325467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9556907418609284248804981 895960070494620398325467)
                      ·
                        rfl

theorem cell23_1744876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1744876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744876 prefixEnd_1744876 := by exact prefixLift 1744876
  have htrace : WordTrace (prefixWord ++ tailWord_1744876) baseStart_1744876 baseEnd_1744876 := by
    simpa [prefixWord, tailWord_1744876, baseEnd_1744876] using wordTrace_append hprefix tailTrace_1744876
  have hstable : (prefixWord ++ tailWord_1744876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744876).length < 2 ^ (prefixWord ++ tailWord_1744876).sum := by decide
  have hdescent : baseEnd_1744876 < baseStart_1744876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744877 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1744877 : Nat := 118140960795 + 1744877 * 2 ^ 59
def prefixEnd_1744877 : Nat := 4983230072969 + 3 ^ 40 * 1744877 * 2
def baseEnd_1744877 : Nat := 895960583975274894412963

theorem tailTrace_1744877 : CollatzResearch.WordTrace tailWord_1744877 prefixEnd_1744877 895960583975274894412963 := by
  unfold tailWord_1744877
  simp only [CollatzResearch.WordTrace]
  refine ⟨63640892499616105111616885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42427261666410736741077923 63640892499616105111616885)
  ·
    refine ⟨5966333671839009854214083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63640892499616105111616885 5966333671839009854214083)
    ·
      refine ⟨8949500507758514781321125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5966333671839009854214083 8949500507758514781321125)
      ·
        refine ⟨1678031345204721521497711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8949500507758514781321125 1678031345204721521497711)
        ·
          refine ⟨2517047017807082282246567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678031345204721521497711 2517047017807082282246567)
          ·
            refine ⟨3775570526710623423369851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517047017807082282246567 3775570526710623423369851)
            ·
              refine ⟨5663355790065935135054777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775570526710623423369851 5663355790065935135054777)
              ·
                refine ⟨4247516842549451351291083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663355790065935135054777 4247516842549451351291083)
                ·
                  refine ⟨6371275263824177026936625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247516842549451351291083 6371275263824177026936625)
                  ·
                    refine ⟨4778456447868132770202469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6371275263824177026936625 4778456447868132770202469)
                    ·
                      refine ⟨895960583975274894412963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4778456447868132770202469 895960583975274894412963)
                      ·
                        rfl

theorem cell23_1744877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1744877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744877 prefixEnd_1744877 := by exact prefixLift 1744877
  have htrace : WordTrace (prefixWord ++ tailWord_1744877) baseStart_1744877 baseEnd_1744877 := by
    simpa [prefixWord, tailWord_1744877, baseEnd_1744877] using wordTrace_append hprefix tailTrace_1744877
  have hstable : (prefixWord ++ tailWord_1744877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744877).length < 2 ^ (prefixWord ++ tailWord_1744877).sum := by decide
  have hdescent : baseEnd_1744877 < baseStart_1744877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744897 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_1744897 : Nat := 118140960795 + 1744897 * 2 ^ 59
def prefixEnd_1744897 : Nat := 4983230072969 + 3 ^ 40 * 1744897 * 2
def baseEnd_1744897 : Nat := 895970853588364816162871

theorem tailTrace_1744897 : CollatzResearch.WordTrace tailWord_1744897 prefixEnd_1744897 895970853588364816162871 := by
  unfold tailWord_1744897
  simp only [CollatzResearch.WordTrace]
  refine ⟨63641621959543648527344945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42427747973029099018229963 63641621959543648527344945)
  ·
    refine ⟨47731216469657736395508709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63641621959543648527344945 47731216469657736395508709)
    ·
      refine ⟨8949603088060825574157883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47731216469657736395508709 8949603088060825574157883)
      ·
        refine ⟨13424404632091238361236825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8949603088060825574157883 13424404632091238361236825)
        ·
          refine ⟨10068303474068428770927619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13424404632091238361236825 10068303474068428770927619)
          ·
            refine ⟨15102455211102643156391429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068303474068428770927619 15102455211102643156391429)
            ·
              refine ⟨2831710352081745591823393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15102455211102643156391429 2831710352081745591823393)
              ·
                refine ⟨2123782764061309193867545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831710352081745591823393 2123782764061309193867545)
                ·
                  refine ⟨1592837073045981895400659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2123782764061309193867545 1592837073045981895400659)
                  ·
                    refine ⟨2389255609568972843100989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1592837073045981895400659 2389255609568972843100989)
                    ·
                      refine ⟨895970853588364816162871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389255609568972843100989 895970853588364816162871)
                      ·
                        rfl

theorem cell23_1744897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_1744897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744897 prefixEnd_1744897 := by exact prefixLift 1744897
  have htrace : WordTrace (prefixWord ++ tailWord_1744897) baseStart_1744897 baseEnd_1744897 := by
    simpa [prefixWord, tailWord_1744897, baseEnd_1744897] using wordTrace_append hprefix tailTrace_1744897
  have hstable : (prefixWord ++ tailWord_1744897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744897).length < 2 ^ (prefixWord ++ tailWord_1744897).sum := by decide
  have hdescent : baseEnd_1744897 < baseStart_1744897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744903 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1744903 : Nat := 118140960795 + 1744903 * 2 ^ 59
def prefixEnd_1744903 : Nat := 4983230072969 + 3 ^ 40 * 1744903 * 2
def baseEnd_1744903 : Nat := 895973934472291792687843

theorem tailTrace_1744903 : CollatzResearch.WordTrace tailWord_1744903 prefixEnd_1744903 895973934472291792687843 := by
  unfold tailWord_1744903
  simp only [CollatzResearch.WordTrace]
  refine ⟨63641840797521911552063363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42427893865014607701375575 63641840797521911552063363)
  ·
    refine ⟨95462761196282867328095045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63641840797521911552063363 95462761196282867328095045)
    ·
      refine ⟨17899267724303037624017821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95462761196282867328095045 17899267724303037624017821)
      ·
        refine ⟨6712225396613639109006683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17899267724303037624017821 6712225396613639109006683)
        ·
          refine ⟨10068338094920458663510025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712225396613639109006683 10068338094920458663510025)
          ·
            refine ⟨7551253571190343997632519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10068338094920458663510025 7551253571190343997632519)
            ·
              refine ⟨11326880356785515996448779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551253571190343997632519 11326880356785515996448779)
              ·
                refine ⟨16990320535178273994673169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11326880356785515996448779 16990320535178273994673169)
                ·
                  refine ⟨12742740401383705496004877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16990320535178273994673169 12742740401383705496004877)
                  ·
                    refine ⟨4778527650518889561001829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12742740401383705496004877 4778527650518889561001829)
                    ·
                      refine ⟨895973934472291792687843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4778527650518889561001829 895973934472291792687843)
                      ·
                        rfl

theorem cell23_1744903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1744903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744903 prefixEnd_1744903 := by exact prefixLift 1744903
  have htrace : WordTrace (prefixWord ++ tailWord_1744903) baseStart_1744903 baseEnd_1744903 := by
    simpa [prefixWord, tailWord_1744903, baseEnd_1744903] using wordTrace_append hprefix tailTrace_1744903
  have hstable : (prefixWord ++ tailWord_1744903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744903).length < 2 ^ (prefixWord ++ tailWord_1744903).sum := by decide
  have hdescent : baseEnd_1744903 < baseStart_1744903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744948 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1744948 : Nat := 118140960795 + 1744948 * 2 ^ 59
def prefixEnd_1744948 : Nat := 4983230072969 + 3 ^ 40 * 1744948 * 2
def baseEnd_1744948 : Nat := 895997041101744116625137

theorem tailTrace_1744948 : CollatzResearch.WordTrace tailWord_1744948 prefixEnd_1744948 895997041101744116625137 := by
  unfold tailWord_1744948
  simp only [CollatzResearch.WordTrace]
  refine ⟨31821741041179442118725749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42428988054905922824967665 31821741041179442118725749)
  ·
    refine ⟨2983288222610572698630539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31821741041179442118725749 2983288222610572698630539)
    ·
      refine ⟨4474932333915859047945809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983288222610572698630539 4474932333915859047945809)
      ·
        refine ⟨3356199250436894285959357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4474932333915859047945809 3356199250436894285959357)
        ·
          refine ⟨1258574718913835357234759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3356199250436894285959357 1258574718913835357234759)
          ·
            refine ⟨1887862078370753035852139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258574718913835357234759 1887862078370753035852139)
            ·
              refine ⟨2831793117556129553778209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887862078370753035852139 2831793117556129553778209)
              ·
                refine ⟨2123844838167097165333657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831793117556129553778209 2123844838167097165333657)
                ·
                  refine ⟨1592883628625322874000243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2123844838167097165333657 1592883628625322874000243)
                  ·
                    refine ⟨2389325442937984311000365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1592883628625322874000243 2389325442937984311000365)
                    ·
                      refine ⟨895997041101744116625137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389325442937984311000365 895997041101744116625137)
                      ·
                        rfl

theorem cell23_1744948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1744948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744948 prefixEnd_1744948 := by exact prefixLift 1744948
  have htrace : WordTrace (prefixWord ++ tailWord_1744948) baseStart_1744948 baseEnd_1744948 := by
    simpa [prefixWord, tailWord_1744948, baseEnd_1744948] using wordTrace_append hprefix tailTrace_1744948
  have hstable : (prefixWord ++ tailWord_1744948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744948).length < 2 ^ (prefixWord ++ tailWord_1744948).sum := by decide
  have hdescent : baseEnd_1744948 < baseStart_1744948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744950 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1744950 : Nat := 118140960795 + 1744950 * 2 ^ 59
def prefixEnd_1744950 : Nat := 4983230072969 + 3 ^ 40 * 1744950 * 2
def baseEnd_1744950 : Nat := 895998068063053108800127

theorem tailTrace_1744950 : CollatzResearch.WordTrace tailWord_1744950 prefixEnd_1744950 895998068063053108800127 := by
  unfold tailWord_1744950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977722189271977411189019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42429036685567759052682869 3977722189271977411189019)
  ·
    refine ⟨5966583283907966116783529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3977722189271977411189019 5966583283907966116783529)
    ·
      refine ⟨4474937462930974587587647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5966583283907966116783529 4474937462930974587587647)
      ·
        refine ⟨6712406194396461881381471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474937462930974587587647 6712406194396461881381471)
        ·
          refine ⟨10068609291594692822072207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712406194396461881381471 10068609291594692822072207)
          ·
            refine ⟨15102913937392039233108311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068609291594692822072207 15102913937392039233108311)
            ·
              refine ⟨22654370906088058849662467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15102913937392039233108311 22654370906088058849662467)
              ·
                refine ⟨33981556359132088274493701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22654370906088058849662467 33981556359132088274493701)
                ·
                  refine ⟨6371541817337266551467569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33981556359132088274493701 6371541817337266551467569)
                  ·
                    refine ⟨4778656363002949913600677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6371541817337266551467569 4778656363002949913600677)
                    ·
                      refine ⟨895998068063053108800127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4778656363002949913600677 895998068063053108800127)
                      ·
                        rfl

theorem cell23_1744950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1744950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744950 prefixEnd_1744950 := by exact prefixLift 1744950
  have htrace : WordTrace (prefixWord ++ tailWord_1744950) baseStart_1744950 baseEnd_1744950 := by
    simpa [prefixWord, tailWord_1744950, baseEnd_1744950] using wordTrace_append hprefix tailTrace_1744950
  have hstable : (prefixWord ++ tailWord_1744950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744950).length < 2 ^ (prefixWord ++ tailWord_1744950).sum := by decide
  have hdescent : baseEnd_1744950 < baseStart_1744950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744960 : List Nat := [2, 1, 1, 2, 2, 4, 2, 4, 5]
def baseStart_1744960 : Nat := 118140960795 + 1744960 * 2 ^ 59
def prefixEnd_1744960 : Nat := 4983230072969 + 3 ^ 40 * 1744960 * 2
def baseEnd_1744960 : Nat := 99555911429955341075009

theorem tailTrace_1744960 : CollatzResearch.WordTrace tailWord_1744960 prefixEnd_1744960 99555911429955341075009 := by
  unfold tailWord_1744960
  simp only [CollatzResearch.WordTrace]
  refine ⟨31821959879157705143444167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42429279838876940191258889 31821959879157705143444167)
  ·
    refine ⟨47732939818736557715166251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31821959879157705143444167 47732939818736557715166251)
    ·
      refine ⟨71599409728104836572749377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47732939818736557715166251 71599409728104836572749377)
      ·
        refine ⟨53699557296078627429562033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71599409728104836572749377 53699557296078627429562033)
        ·
          refine ⟨40274667972058970572171525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53699557296078627429562033 40274667972058970572171525)
          ·
            refine ⟨7551500244761056982282161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40274667972058970572171525 7551500244761056982282161)
            ·
              refine ⟨5663625183570792736711621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7551500244761056982282161 5663625183570792736711621)
              ·
                refine ⟨1061929721919523638133429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5663625183570792736711621 1061929721919523638133429)
                ·
                  refine ⟨99555911429955341075009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1061929721919523638133429 99555911429955341075009)
                  ·
                    rfl

theorem cell23_1744960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 5].length) (baseStart_1744960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744960 prefixEnd_1744960 := by exact prefixLift 1744960
  have htrace : WordTrace (prefixWord ++ tailWord_1744960) baseStart_1744960 baseEnd_1744960 := by
    simpa [prefixWord, tailWord_1744960, baseEnd_1744960] using wordTrace_append hprefix tailTrace_1744960
  have hstable : (prefixWord ++ tailWord_1744960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744960).length < 2 ^ (prefixWord ++ tailWord_1744960).sum := by decide
  have hdescent : baseEnd_1744960 < baseStart_1744960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745010 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1745010 : Nat := 118140960795 + 1745010 * 2 ^ 59
def prefixEnd_1745010 : Nat := 4983230072969 + 3 ^ 40 * 1745010 * 2
def baseEnd_1745010 : Nat := 896028876902322874049851

theorem tailTrace_1745010 : CollatzResearch.WordTrace tailWord_1745010 prefixEnd_1745010 896028876902322874049851 := by
  unfold tailWord_1745010
  simp only [CollatzResearch.WordTrace]
  refine ⟨15911435852033567206552121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42430495605422845884138989 15911435852033567206552121)
  ·
    refine ⟨11933576889025175404914091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15911435852033567206552121 11933576889025175404914091)
    ·
      refine ⟨17900365333537763107371137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11933576889025175404914091 17900365333537763107371137)
      ·
        refine ⟨13425274000153322330528353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17900365333537763107371137 13425274000153322330528353)
        ·
          refine ⟨10068955500114991747896265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13425274000153322330528353 10068955500114991747896265)
          ·
            refine ⟨7551716625086243810922199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10068955500114991747896265 7551716625086243810922199)
            ·
              refine ⟨11327574937629365716383299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551716625086243810922199 11327574937629365716383299)
              ·
                refine ⟨16991362406444048574574949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11327574937629365716383299 16991362406444048574574949)
                ·
                  refine ⟨3185880451208259107732803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16991362406444048574574949 3185880451208259107732803)
                  ·
                    refine ⟨4778820676812388661599205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3185880451208259107732803 4778820676812388661599205)
                    ·
                      refine ⟨896028876902322874049851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4778820676812388661599205 896028876902322874049851)
                      ·
                        rfl

theorem cell23_1745010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1745010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745010 prefixEnd_1745010 := by exact prefixLift 1745010
  have htrace : WordTrace (prefixWord ++ tailWord_1745010) baseStart_1745010 baseEnd_1745010 := by
    simpa [prefixWord, tailWord_1745010, baseEnd_1745010] using wordTrace_append hprefix tailTrace_1745010
  have hstable : (prefixWord ++ tailWord_1745010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745010).length < 2 ^ (prefixWord ++ tailWord_1745010).sum := by decide
  have hdescent : baseEnd_1745010 < baseStart_1745010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745120 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1745120 : Nat := 118140960795 + 1745120 * 2 ^ 59
def prefixEnd_1745120 : Nat := 4983230072969 + 3 ^ 40 * 1745120 * 2
def baseEnd_1745120 : Nat := 896085359774317443674345

theorem tailTrace_1745120 : CollatzResearch.WordTrace tailWord_1745120 prefixEnd_1745120 896085359774317443674345 := by
  unfold tailWord_1745120
  simp only [CollatzResearch.WordTrace]
  refine ⟨31824877718867878806356407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42433170291823838408475209 31824877718867878806356407)
  ·
    refine ⟨47737316578301818209534611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31824877718867878806356407 47737316578301818209534611)
    ·
      refine ⟨71605974867452727314301917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47737316578301818209534611 71605974867452727314301917)
      ·
        refine ⟨26852240575294772742863219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71605974867452727314301917 26852240575294772742863219)
        ·
          refine ⟨40278360862942159114294829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26852240575294772742863219 40278360862942159114294829)
          ·
            refine ⟨15104385323603309667860561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40278360862942159114294829 15104385323603309667860561)
            ·
              refine ⟨11328288992702482250895421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15104385323603309667860561 11328288992702482250895421)
              ·
                refine ⟨4248108372263430844085783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11328288992702482250895421 4248108372263430844085783)
                ·
                  refine ⟨6372162558395146266128675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248108372263430844085783 6372162558395146266128675)
                  ·
                    refine ⟨9558243837592719399193013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6372162558395146266128675 9558243837592719399193013)
                    ·
                      refine ⟨896085359774317443674345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9558243837592719399193013 896085359774317443674345)
                      ·
                        rfl

theorem cell23_1745120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1745120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745120 prefixEnd_1745120 := by exact prefixLift 1745120
  have htrace : WordTrace (prefixWord ++ tailWord_1745120) baseStart_1745120 baseEnd_1745120 := by
    simpa [prefixWord, tailWord_1745120, baseEnd_1745120] using wordTrace_append hprefix tailTrace_1745120
  have hstable : (prefixWord ++ tailWord_1745120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745120).length < 2 ^ (prefixWord ++ tailWord_1745120).sum := by decide
  have hdescent : baseEnd_1745120 < baseStart_1745120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745130 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1745130 : Nat := 118140960795 + 1745130 * 2 ^ 59
def prefixEnd_1745130 : Nat := 4983230072969 + 3 ^ 40 * 1745130 * 2
def baseEnd_1745130 : Nat := 896090494580862404549299

theorem tailTrace_1745130 : CollatzResearch.WordTrace tailWord_1745130 prefixEnd_1745130 896090494580862404549299 := by
  unfold tailWord_1745130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15912530041924882330144211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42433413445133019547051229 15912530041924882330144211)
  ·
    refine ⟨23868795062887323495216317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15912530041924882330144211 23868795062887323495216317)
    ·
      refine ⟨8950798148582746310706119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23868795062887323495216317 8950798148582746310706119)
      ·
        refine ⟨13426197222874119466059179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8950798148582746310706119 13426197222874119466059179)
        ·
          refine ⟨20139295834311179199088769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426197222874119466059179 20139295834311179199088769)
          ·
            refine ⟨15104471875733384399316577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20139295834311179199088769 15104471875733384399316577)
            ·
              refine ⟨11328353906800038299487433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15104471875733384399316577 11328353906800038299487433)
              ·
                refine ⟨8496265430100028724615575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11328353906800038299487433 8496265430100028724615575)
                ·
                  refine ⟨12744398145150043086923363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8496265430100028724615575 12744398145150043086923363)
                  ·
                    refine ⟨19116597217725064630385045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12744398145150043086923363 19116597217725064630385045)
                    ·
                      refine ⟨896090494580862404549299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19116597217725064630385045 896090494580862404549299)
                      ·
                        rfl

theorem cell23_1745130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1745130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745130 prefixEnd_1745130 := by exact prefixLift 1745130
  have htrace : WordTrace (prefixWord ++ tailWord_1745130) baseStart_1745130 baseEnd_1745130 := by
    simpa [prefixWord, tailWord_1745130, baseEnd_1745130] using wordTrace_append hprefix tailTrace_1745130
  have hstable : (prefixWord ++ tailWord_1745130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745130).length < 2 ^ (prefixWord ++ tailWord_1745130).sum := by decide
  have hdescent : baseEnd_1745130 < baseStart_1745130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745180 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1745180 : Nat := 118140960795 + 1745180 * 2 ^ 59
def prefixEnd_1745180 : Nat := 4983230072969 + 3 ^ 40 * 1745180 * 2
def baseEnd_1745180 : Nat := 896116168613587208924069

theorem tailTrace_1745180 : CollatzResearch.WordTrace tailWord_1745180 prefixEnd_1745180 896116168613587208924069 := by
  unfold tailWord_1745180
  simp only [CollatzResearch.WordTrace]
  refine ⟨31825971908759193929948497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42434629211678925239931329 31825971908759193929948497)
  ·
    refine ⟨23869478931569395447461373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31825971908759193929948497 23869478931569395447461373)
    ·
      refine ⟨8951054599338523292798015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23869478931569395447461373 8951054599338523292798015)
      ·
        refine ⟨13426581899007784939197023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8951054599338523292798015 13426581899007784939197023)
        ·
          refine ⟨20139872848511677408795535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426581899007784939197023 20139872848511677408795535)
          ·
            refine ⟨30209809272767516113193303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20139872848511677408795535 30209809272767516113193303)
            ·
              refine ⟨45314713909151274169789955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30209809272767516113193303 45314713909151274169789955)
              ·
                refine ⟨67972070863726911254684933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45314713909151274169789955 67972070863726911254684933)
                ·
                  refine ⟨12744763286948795860253425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67972070863726911254684933 12744763286948795860253425)
                  ·
                    refine ⟨9558572465211596895190069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12744763286948795860253425 9558572465211596895190069)
                    ·
                      refine ⟨896116168613587208924069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9558572465211596895190069 896116168613587208924069)
                      ·
                        rfl

theorem cell23_1745180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1745180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745180 prefixEnd_1745180 := by exact prefixLift 1745180
  have htrace : WordTrace (prefixWord ++ tailWord_1745180) baseStart_1745180 baseEnd_1745180 := by
    simpa [prefixWord, tailWord_1745180, baseEnd_1745180] using wordTrace_append hprefix tailTrace_1745180
  have hstable : (prefixWord ++ tailWord_1745180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745180).length < 2 ^ (prefixWord ++ tailWord_1745180).sum := by decide
  have hdescent : baseEnd_1745180 < baseStart_1745180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745184 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1745184 : Nat := 118140960795 + 1745184 * 2 ^ 59
def prefixEnd_1745184 : Nat := 4983230072969 + 3 ^ 40 * 1745184 * 2
def baseEnd_1745184 : Nat := 896118222536205193274051

theorem tailTrace_1745184 : CollatzResearch.WordTrace tailWord_1745184 prefixEnd_1745184 896118222536205193274051 := by
  unfold tailWord_1745184
  simp only [CollatzResearch.WordTrace]
  refine ⟨31826044854751948271521303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42434726473002597695361737 31826044854751948271521303)
  ·
    refine ⟨47739067282127922407281955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31826044854751948271521303 47739067282127922407281955)
    ·
      refine ⟨71608600923191883610922933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47739067282127922407281955 71608600923191883610922933)
      ·
        refine ⟨6713306336549239088524025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71608600923191883610922933 6713306336549239088524025)
        ·
          refine ⟨5034979752411929316393019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6713306336549239088524025 5034979752411929316393019)
          ·
            refine ⟨7552469628617893974589529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034979752411929316393019 7552469628617893974589529)
            ·
              refine ⟨5664352221463420480942147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7552469628617893974589529 5664352221463420480942147)
              ·
                refine ⟨8496528332195130721413221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664352221463420480942147 8496528332195130721413221)
                ·
                  refine ⟨1593099062286587010264979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8496528332195130721413221 1593099062286587010264979)
                  ·
                    refine ⟨2389648593429880515397469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1593099062286587010264979 2389648593429880515397469)
                    ·
                      refine ⟨896118222536205193274051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389648593429880515397469 896118222536205193274051)
                      ·
                        rfl

theorem cell23_1745184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1745184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745184 prefixEnd_1745184 := by exact prefixLift 1745184
  have htrace : WordTrace (prefixWord ++ tailWord_1745184) baseStart_1745184 baseEnd_1745184 := by
    simpa [prefixWord, tailWord_1745184, baseEnd_1745184] using wordTrace_append hprefix tailTrace_1745184
  have hstable : (prefixWord ++ tailWord_1745184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745184).length < 2 ^ (prefixWord ++ tailWord_1745184).sum := by decide
  have hdescent : baseEnd_1745184 < baseStart_1745184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745191 : List Nat := [1, 1, 8, 1, 1, 1, 2, 8]
def baseStart_1745191 : Nat := 118140960795 + 1745191 * 2 ^ 59
def prefixEnd_1745191 : Nat := 4983230072969 + 3 ^ 40 * 1745191 * 2
def baseEnd_1745191 : Nat := 33189696922251357995797

theorem tailTrace_1745191 : CollatzResearch.WordTrace tailWord_1745191 prefixEnd_1745191 33189696922251357995797 := by
  unfold tailWord_1745191
  simp only [CollatzResearch.WordTrace]
  refine ⟨63652345020478536738547427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42434896680319024492364951 63652345020478536738547427)
  ·
    refine ⟨95478517530717805107821141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63652345020478536738547427 95478517530717805107821141)
    ·
      refine ⟨1118888877313099278607279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 95478517530717805107821141 1118888877313099278607279)
      ·
        refine ⟨1678333315969648917910919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118888877313099278607279 1678333315969648917910919)
        ·
          refine ⟨2517499973954473376866379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678333315969648917910919 2517499973954473376866379)
          ·
            refine ⟨3776249960931710065299569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517499973954473376866379 3776249960931710065299569)
            ·
              refine ⟨2832187470698782548974677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3776249960931710065299569 2832187470698782548974677)
              ·
                refine ⟨33189696922251357995797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2832187470698782548974677 33189696922251357995797)
                ·
                  rfl

theorem cell23_1745191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 8].length) (baseStart_1745191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745191 prefixEnd_1745191 := by exact prefixLift 1745191
  have htrace : WordTrace (prefixWord ++ tailWord_1745191) baseStart_1745191 baseEnd_1745191 := by
    simpa [prefixWord, tailWord_1745191, baseEnd_1745191] using wordTrace_append hprefix tailTrace_1745191
  have hstable : (prefixWord ++ tailWord_1745191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745191).length < 2 ^ (prefixWord ++ tailWord_1745191).sum := by decide
  have hdescent : baseEnd_1745191 < baseStart_1745191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745201 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_1745201 : Nat := 118140960795 + 1745201 * 2 ^ 59
def prefixEnd_1745201 : Nat := 4983230072969 + 3 ^ 40 * 1745201 * 2
def baseEnd_1745201 : Nat := 896126951707331626761473

theorem tailTrace_1745201 : CollatzResearch.WordTrace tailWord_1745201 prefixEnd_1745201 896126951707331626761473 := by
  unfold tailWord_1745201
  simp only [CollatzResearch.WordTrace]
  refine ⟨63652709750442308446411457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42435139833628205630940971 63652709750442308446411457)
  ·
    refine ⟨47739532312831731334808593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63652709750442308446411457 47739532312831731334808593)
    ·
      refine ⟨35804649234623798501106445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47739532312831731334808593 35804649234623798501106445)
      ·
        refine ⟨13426743462983924437914917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35804649234623798501106445 13426743462983924437914917)
        ·
          refine ⟨2517514399309485832109047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13426743462983924437914917 2517514399309485832109047)
          ·
            refine ⟨3776271598964228748163571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517514399309485832109047 3776271598964228748163571)
            ·
              refine ⟨5664407398446343122245357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776271598964228748163571 5664407398446343122245357)
              ·
                refine ⟨2124152774417378670842009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664407398446343122245357 2124152774417378670842009)
                ·
                  refine ⟨1593114580813034003131507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2124152774417378670842009 1593114580813034003131507)
                  ·
                    refine ⟨2389671871219551004697261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1593114580813034003131507 2389671871219551004697261)
                    ·
                      refine ⟨896126951707331626761473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389671871219551004697261 896126951707331626761473)
                      ·
                        rfl

theorem cell23_1745201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_1745201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745201 prefixEnd_1745201 := by exact prefixLift 1745201
  have htrace : WordTrace (prefixWord ++ tailWord_1745201) baseStart_1745201 baseEnd_1745201 := by
    simpa [prefixWord, tailWord_1745201, baseEnd_1745201] using wordTrace_append hprefix tailTrace_1745201
  have hstable : (prefixWord ++ tailWord_1745201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745201).length < 2 ^ (prefixWord ++ tailWord_1745201).sum := by decide
  have hdescent : baseEnd_1745201 < baseStart_1745201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745207 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 5, 4, 2]
def baseStart_1745207 : Nat := 118140960795 + 1745207 * 2 ^ 59
def prefixEnd_1745207 : Nat := 4983230072969 + 3 ^ 40 * 1745207 * 2
def baseEnd_1745207 : Nat := 896130032591258603286445

theorem tailTrace_1745207 : CollatzResearch.WordTrace tailWord_1745207 prefixEnd_1745207 896130032591258603286445 := by
  unfold tailWord_1745207
  simp only [CollatzResearch.WordTrace]
  refine ⟨63652928588420571471129875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42435285725613714314086583 63652928588420571471129875)
  ·
    refine ⟨95479392882630857206694813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63652928588420571471129875 95479392882630857206694813)
    ·
      refine ⟨35804772330986571452510555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95479392882630857206694813 35804772330986571452510555)
      ·
        refine ⟨53707158496479857178765833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35804772330986571452510555 53707158496479857178765833)
        ·
          refine ⟨40280368872359892884074375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53707158496479857178765833 40280368872359892884074375)
          ·
            refine ⟨60420553308539839326111563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40280368872359892884074375 60420553308539839326111563)
            ·
              refine ⟨90630829962809758989167345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60420553308539839326111563 90630829962809758989167345)
              ·
                refine ⟨67973122472107319241875509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90630829962809758989167345 67973122472107319241875509)
                ·
                  refine ⟨6372480231760061178925829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67973122472107319241875509 6372480231760061178925829)
                  ·
                    refine ⟨1194840043455011471048593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6372480231760061178925829 1194840043455011471048593)
                    ·
                      refine ⟨896130032591258603286445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194840043455011471048593 896130032591258603286445)
                      ·
                        rfl

theorem cell23_1745207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_1745207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745207 prefixEnd_1745207 := by exact prefixLift 1745207
  have htrace : WordTrace (prefixWord ++ tailWord_1745207) baseStart_1745207 baseEnd_1745207 := by
    simpa [prefixWord, tailWord_1745207, baseEnd_1745207] using wordTrace_append hprefix tailTrace_1745207
  have hstable : (prefixWord ++ tailWord_1745207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745207).length < 2 ^ (prefixWord ++ tailWord_1745207).sum := by decide
  have hdescent : baseEnd_1745207 < baseStart_1745207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745224 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_1745224 : Nat := 118140960795 + 1745224 * 2 ^ 59
def prefixEnd_1745224 : Nat := 4983230072969 + 3 ^ 40 * 1745224 * 2
def baseEnd_1745224 : Nat := 896138761762385036773867

theorem tailTrace_1745224 : CollatzResearch.WordTrace tailWord_1745224 prefixEnd_1745224 896138761762385036773867 := by
  unfold tailWord_1745224
  simp only [CollatzResearch.WordTrace]
  refine ⟨31826774314679491687249363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42435699086239322249665817 31826774314679491687249363)
  ·
    refine ⟨47740161472019237530874045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31826774314679491687249363 47740161472019237530874045)
    ·
      refine ⟨17902560552007214074077767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47740161472019237530874045 17902560552007214074077767)
      ·
        refine ⟨26853840828010821111116651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17902560552007214074077767 26853840828010821111116651)
        ·
          refine ⟨40280761242016231666674977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26853840828010821111116651 40280761242016231666674977)
          ·
            refine ⟨30210570931512173750006233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40280761242016231666674977 30210570931512173750006233)
            ·
              refine ⟨22657928198634130312504675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30210570931512173750006233 22657928198634130312504675)
              ·
                refine ⟨33986892297951195468757013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22657928198634130312504675 33986892297951195468757013)
                ·
                  refine ⟨1593135576466462287597985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33986892297951195468757013 1593135576466462287597985)
                  ·
                    refine ⟨1194851682349846715698489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1593135576466462287597985 1194851682349846715698489)
                    ·
                      refine ⟨896138761762385036773867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194851682349846715698489 896138761762385036773867)
                      ·
                        rfl

theorem cell23_1745224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_1745224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745224 prefixEnd_1745224 := by exact prefixLift 1745224
  have htrace : WordTrace (prefixWord ++ tailWord_1745224) baseStart_1745224 baseEnd_1745224 := by
    simpa [prefixWord, tailWord_1745224, baseEnd_1745224] using wordTrace_append hprefix tailTrace_1745224
  have hstable : (prefixWord ++ tailWord_1745224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745224).length < 2 ^ (prefixWord ++ tailWord_1745224).sum := by decide
  have hdescent : baseEnd_1745224 < baseStart_1745224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745230 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_1745230 : Nat := 118140960795 + 1745230 * 2 ^ 59
def prefixEnd_1745230 : Nat := 4983230072969 + 3 ^ 40 * 1745230 * 2
def baseEnd_1745230 : Nat := 99571315849590223699871

theorem tailTrace_1745230 : CollatzResearch.WordTrace tailWord_1745230 prefixEnd_1745230 99571315849590223699871 := by
  unfold tailWord_1745230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956720933417155799902143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42435844978224830932811429 7956720933417155799902143)
  ·
    refine ⟨11935081400125733699853215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7956720933417155799902143 11935081400125733699853215)
    ·
      refine ⟨17902622100188600549779823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11935081400125733699853215 17902622100188600549779823)
      ·
        refine ⟨26853933150282900824669735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17902622100188600549779823 26853933150282900824669735)
        ·
          refine ⟨40280899725424351237004603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26853933150282900824669735 40280899725424351237004603)
          ·
            refine ⟨60421349588136526855506905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40280899725424351237004603 60421349588136526855506905)
            ·
              refine ⟨45316012191102395141630179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60421349588136526855506905 45316012191102395141630179)
              ·
                refine ⟨67974018286653592712445269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45316012191102395141630179 67974018286653592712445269)
                ·
                  refine ⟨99571315849590223699871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 67974018286653592712445269 99571315849590223699871)
                  ·
                    rfl

theorem cell23_1745230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_1745230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745230 prefixEnd_1745230 := by exact prefixLift 1745230
  have htrace : WordTrace (prefixWord ++ tailWord_1745230) baseStart_1745230 baseEnd_1745230 := by
    simpa [prefixWord, tailWord_1745230, baseEnd_1745230] using wordTrace_append hprefix tailTrace_1745230
  have hstable : (prefixWord ++ tailWord_1745230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745230).length < 2 ^ (prefixWord ++ tailWord_1745230).sum := by decide
  have hdescent : baseEnd_1745230 < baseStart_1745230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745257 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 3]
def baseStart_1745257 : Nat := 118140960795 + 1745257 * 2 ^ 59
def prefixEnd_1745257 : Nat := 4983230072969 + 3 ^ 40 * 1745257 * 2
def baseEnd_1745257 : Nat := 896155706623983407661215

theorem tailTrace_1745257 : CollatzResearch.WordTrace tailWord_1745257 prefixEnd_1745257 896155706623983407661215 := by
  unfold tailWord_1745257
  simp only [CollatzResearch.WordTrace]
  refine ⟨63654752238239430010450025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42436501492159620006966683 63654752238239430010450025)
  ·
    refine ⟨47741064178679572507837519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63654752238239430010450025 47741064178679572507837519)
    ·
      refine ⟨71611596268019358761756279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47741064178679572507837519 71611596268019358761756279)
      ·
        refine ⟨107417394402029038142634419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71611596268019358761756279 107417394402029038142634419)
        ·
          refine ⟨161126091603043557213951629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107417394402029038142634419 161126091603043557213951629)
          ·
            refine ⟨60422284351141333955231861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161126091603043557213951629 60422284351141333955231861)
            ·
              refine ⟨5664589157919500058302987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60422284351141333955231861 5664589157919500058302987)
              ·
                refine ⟨8496883736879250087454481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664589157919500058302987 8496883736879250087454481)
                ·
                  refine ⟨6372662802659437565590861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8496883736879250087454481 6372662802659437565590861)
                  ·
                    refine ⟨2389748550997289087096573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6372662802659437565590861 2389748550997289087096573)
                    ·
                      refine ⟨896155706623983407661215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389748550997289087096573 896155706623983407661215)
                      ·
                        rfl

theorem cell23_1745257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_1745257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745257 prefixEnd_1745257 := by exact prefixLift 1745257
  have htrace : WordTrace (prefixWord ++ tailWord_1745257) baseStart_1745257 baseEnd_1745257 := by
    simpa [prefixWord, tailWord_1745257, baseEnd_1745257] using wordTrace_append hprefix tailTrace_1745257
  have hstable : (prefixWord ++ tailWord_1745257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745257).length < 2 ^ (prefixWord ++ tailWord_1745257).sum := by decide
  have hdescent : baseEnd_1745257 < baseStart_1745257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745258 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1745258 : Nat := 118140960795 + 1745258 * 2 ^ 59
def prefixEnd_1745258 : Nat := 4983230072969 + 3 ^ 40 * 1745258 * 2
def baseEnd_1745258 : Nat := 896156220104637903748711

theorem tailTrace_1745258 : CollatzResearch.WordTrace tailWord_1745258 prefixEnd_1745258 896156220104637903748711 := by
  unfold tailWord_1745258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15913697177808951795309107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42436525807490538120824285 15913697177808951795309107)
  ·
    refine ⟨23870545766713427692963661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15913697177808951795309107 23870545766713427692963661)
    ·
      refine ⟨8951454662517535384861373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23870545766713427692963661 8951454662517535384861373)
      ·
        refine ⟨3356795498444075769323015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8951454662517535384861373 3356795498444075769323015)
        ·
          refine ⟨5035193247666113653984523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356795498444075769323015 5035193247666113653984523)
          ·
            refine ⟨7552789871499170480976785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035193247666113653984523 7552789871499170480976785)
            ·
              refine ⟨5664592403624377860732589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7552789871499170480976785 5664592403624377860732589)
              ·
                refine ⟨2124222151359141697774721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664592403624377860732589 2124222151359141697774721)
                ·
                  refine ⟨1593166613519356273331041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2124222151359141697774721 1593166613519356273331041)
                  ·
                    refine ⟨1194874960139517204998281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1593166613519356273331041 1194874960139517204998281)
                    ·
                      refine ⟨896156220104637903748711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194874960139517204998281 896156220104637903748711)
                      ·
                        rfl

theorem cell23_1745258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1745258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745258 prefixEnd_1745258 := by exact prefixLift 1745258
  have htrace : WordTrace (prefixWord ++ tailWord_1745258) baseStart_1745258 baseEnd_1745258 := by
    simpa [prefixWord, tailWord_1745258, baseEnd_1745258] using wordTrace_append hprefix tailTrace_1745258
  have hstable : (prefixWord ++ tailWord_1745258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745258).length < 2 ^ (prefixWord ++ tailWord_1745258).sum := by decide
  have hdescent : baseEnd_1745258 < baseStart_1745258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745277 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1745277 : Nat := 118140960795 + 1745277 * 2 ^ 59
def prefixEnd_1745277 : Nat := 4983230072969 + 3 ^ 40 * 1745277 * 2
def baseEnd_1745277 : Nat := 298721992079024443137041

theorem tailTrace_1745277 : CollatzResearch.WordTrace tailWord_1745277 prefixEnd_1745277 298721992079024443137041 := by
  unfold tailWord_1745277
  simp only [CollatzResearch.WordTrace]
  refine ⟨63655481698166973426178085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42436987798777982284118723 63655481698166973426178085)
  ·
    refine ⟨11935402818406307517408391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63655481698166973426178085 11935402818406307517408391)
    ·
      refine ⟨17903104227609461276112587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11935402818406307517408391 17903104227609461276112587)
      ·
        refine ⟨26854656341414191914168881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17903104227609461276112587 26854656341414191914168881)
        ·
          refine ⟨20140992256060643935626661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26854656341414191914168881 20140992256060643935626661)
          ·
            refine ⟨3776436048011370737929999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20140992256060643935626661 3776436048011370737929999)
            ·
              refine ⟨5664654072017056106894999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776436048011370737929999 5664654072017056106894999)
              ·
                refine ⟨8496981108025584160342499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664654072017056106894999 8496981108025584160342499)
                ·
                  refine ⟨12745471662038376240513749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8496981108025584160342499 12745471662038376240513749)
                  ·
                    refine ⟨298721992079024443137041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12745471662038376240513749 298721992079024443137041)
                    ·
                      rfl

theorem cell23_1745277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1745277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745277 prefixEnd_1745277 := by exact prefixLift 1745277
  have htrace : WordTrace (prefixWord ++ tailWord_1745277) baseStart_1745277 baseEnd_1745277 := by
    simpa [prefixWord, tailWord_1745277, baseEnd_1745277] using wordTrace_append hprefix tailTrace_1745277
  have hstable : (prefixWord ++ tailWord_1745277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745277).length < 2 ^ (prefixWord ++ tailWord_1745277).sum := by decide
  have hdescent : baseEnd_1745277 < baseStart_1745277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745281 : List Nat := [1, 2, 4, 3, 1, 2, 2, 3, 5]
def baseStart_1745281 : Nat := 118140960795 + 1745281 * 2 ^ 59
def prefixEnd_1745281 : Nat := 4983230072969 + 3 ^ 40 * 1745281 * 2
def baseEnd_1745281 : Nat := 99574225573299034862345

theorem tailTrace_1745281 : CollatzResearch.WordTrace tailWord_1745281 prefixEnd_1745281 99574225573299034862345 := by
  unfold tailWord_1745281
  simp only [CollatzResearch.WordTrace]
  refine ⟨63655627590152482109323697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42437085060101654739549131 63655627590152482109323697)
  ·
    refine ⟨47741720692614361581992773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63655627590152482109323697 47741720692614361581992773)
    ·
      refine ⟨8951572629865192796623645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47741720692614361581992773 8951572629865192796623645)
      ·
        refine ⟨3356839736199447298733867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8951572629865192796623645 3356839736199447298733867)
        ·
          refine ⟨5035259604299170948100801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356839736199447298733867 5035259604299170948100801)
          ·
            refine ⟨3776444703224378211075601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5035259604299170948100801 3776444703224378211075601)
            ·
              refine ⟨2832333527418283658306701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3776444703224378211075601 2832333527418283658306701)
              ·
                refine ⟨1062125072781856371865013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832333527418283658306701 1062125072781856371865013)
                ·
                  refine ⟨99574225573299034862345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1062125072781856371865013 99574225573299034862345)
                  ·
                    rfl

theorem cell23_1745281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 5].length) (baseStart_1745281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745281 prefixEnd_1745281 := by exact prefixLift 1745281
  have htrace : WordTrace (prefixWord ++ tailWord_1745281) baseStart_1745281 baseEnd_1745281 := by
    simpa [prefixWord, tailWord_1745281, baseEnd_1745281] using wordTrace_append hprefix tailTrace_1745281
  have hstable : (prefixWord ++ tailWord_1745281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745281).length < 2 ^ (prefixWord ++ tailWord_1745281).sum := by decide
  have hdescent : baseEnd_1745281 < baseStart_1745281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745317 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_1745317 : Nat := 118140960795 + 1745317 * 2 ^ 59
def prefixEnd_1745317 : Nat := 4983230072969 + 3 ^ 40 * 1745317 * 2
def baseEnd_1745317 : Nat := 896186515463253172910939

theorem tailTrace_1745317 : CollatzResearch.WordTrace tailWord_1745317 prefixEnd_1745317 896186515463253172910939 := by
  unfold tailWord_1745317
  simp only [CollatzResearch.WordTrace]
  refine ⟨63656940618022060257634205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42437960412014706838422803 63656940618022060257634205)
  ·
    refine ⟨23871352731758272596612827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63656940618022060257634205 23871352731758272596612827)
    ·
      refine ⟨35807029097637408894919241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23871352731758272596612827 35807029097637408894919241)
      ·
        refine ⟨26855271823228056671189431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35807029097637408894919241 26855271823228056671189431)
        ·
          refine ⟨40282907734842085006784147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26855271823228056671189431 40282907734842085006784147)
          ·
            refine ⟨60424361602263127510176221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40282907734842085006784147 60424361602263127510176221)
            ·
              refine ⟨22659135600848672816316083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60424361602263127510176221 22659135600848672816316083)
              ·
                refine ⟨33988703401273009224474125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22659135600848672816316083 33988703401273009224474125)
                ·
                  refine ⟨12745763775477378459177797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33988703401273009224474125 12745763775477378459177797)
                  ·
                    refine ⟨2389830707902008461095837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12745763775477378459177797 2389830707902008461095837)
                    ·
                      refine ⟨896186515463253172910939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389830707902008461095837 896186515463253172910939)
                      ·
                        rfl

theorem cell23_1745317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_1745317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745317 prefixEnd_1745317 := by exact prefixLift 1745317
  have htrace : WordTrace (prefixWord ++ tailWord_1745317) baseStart_1745317 baseEnd_1745317 := by
    simpa [prefixWord, tailWord_1745317, baseEnd_1745317] using wordTrace_append hprefix tailTrace_1745317
  have hstable : (prefixWord ++ tailWord_1745317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745317).length < 2 ^ (prefixWord ++ tailWord_1745317).sum := by decide
  have hdescent : baseEnd_1745317 < baseStart_1745317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745332 : List Nat := [2, 5, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1745332 : Nat := 118140960795 + 1745332 * 2 ^ 59
def prefixEnd_1745332 : Nat := 4983230072969 + 3 ^ 40 * 1745332 * 2
def baseEnd_1745332 : Nat := 99577135297007846024819

theorem tailTrace_1745332 : CollatzResearch.WordTrace tailWord_1745332 prefixEnd_1745332 99577135297007846024819 := by
  unfold tailWord_1745332
  simp only [CollatzResearch.WordTrace]
  refine ⟨31828743856483858909715125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42438325141978478546286833 31828743856483858909715125)
  ·
    refine ⟨2983944736545361772785793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31828743856483858909715125 2983944736545361772785793)
    ·
      refine ⟨2237958552409021329589345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2983944736545361772785793 2237958552409021329589345)
      ·
        refine ⟨1678468914306765997192009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2237958552409021329589345 1678468914306765997192009)
        ·
          refine ⟨1258851685730074497894007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678468914306765997192009 1258851685730074497894007)
          ·
            refine ⟨1888277528595111746841011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258851685730074497894007 1888277528595111746841011)
            ·
              refine ⟨2832416292892667620261517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888277528595111746841011 2832416292892667620261517)
              ·
                refine ⟨1062156109834750357598069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832416292892667620261517 1062156109834750357598069)
                ·
                  refine ⟨99577135297007846024819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1062156109834750357598069 99577135297007846024819)
                  ·
                    rfl

theorem cell23_1745332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1745332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745332 prefixEnd_1745332 := by exact prefixLift 1745332
  have htrace : WordTrace (prefixWord ++ tailWord_1745332) baseStart_1745332 baseEnd_1745332 := by
    simpa [prefixWord, tailWord_1745332, baseEnd_1745332] using wordTrace_append hprefix tailTrace_1745332
  have hstable : (prefixWord ++ tailWord_1745332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745332).length < 2 ^ (prefixWord ++ tailWord_1745332).sum := by decide
  have hdescent : baseEnd_1745332 < baseStart_1745332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745337 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 8]
def baseStart_1745337 : Nat := 118140960795 + 1745337 * 2 ^ 59
def prefixEnd_1745337 : Nat := 4983230072969 + 3 ^ 40 * 1745337 * 2
def baseEnd_1745337 : Nat := 99577420564038121628983

theorem tailTrace_1745337 : CollatzResearch.WordTrace tailWord_1745337 prefixEnd_1745337 99577420564038121628983 := by
  unfold tailWord_1745337
  simp only [CollatzResearch.WordTrace]
  refine ⟨63657670077949603673362265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42438446718633069115574843 63657670077949603673362265)
  ·
    refine ⟨47743252558462202755021699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63657670077949603673362265 47743252558462202755021699)
    ·
      refine ⟨71614878837693304132532549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47743252558462202755021699 71614878837693304132532549)
      ·
        refine ⟨13427789782067494524849853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71614878837693304132532549 13427789782067494524849853)
        ·
          refine ⟨5035421168275310446818695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13427789782067494524849853 5035421168275310446818695)
          ·
            refine ⟨7553131752412965670228043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035421168275310446818695 7553131752412965670228043)
            ·
              refine ⟨11329697628619448505342065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7553131752412965670228043 11329697628619448505342065)
              ·
                refine ⟨8497273221464586379006549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11329697628619448505342065 8497273221464586379006549)
                ·
                  refine ⟨99577420564038121628983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8497273221464586379006549 99577420564038121628983)
                  ·
                    rfl

theorem cell23_1745337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_1745337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745337 prefixEnd_1745337 := by exact prefixLift 1745337
  have htrace : WordTrace (prefixWord ++ tailWord_1745337) baseStart_1745337 baseEnd_1745337 := by
    simpa [prefixWord, tailWord_1745337, baseEnd_1745337] using wordTrace_append hprefix tailTrace_1745337
  have hstable : (prefixWord ++ tailWord_1745337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745337).length < 2 ^ (prefixWord ++ tailWord_1745337).sum := by decide
  have hdescent : baseEnd_1745337 < baseStart_1745337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745384 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1745384 : Nat := 118140960795 + 1745384 * 2 ^ 59
def prefixEnd_1745384 : Nat := 4983230072969 + 3 ^ 40 * 1745384 * 2
def baseEnd_1745384 : Nat := 298740306222368136924377

theorem tailTrace_1745384 : CollatzResearch.WordTrace tailWord_1745384 prefixEnd_1745384 298740306222368136924377 := by
  unfold tailWord_1745384
  simp only [CollatzResearch.WordTrace]
  refine ⟨31829692154389665350161603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42439589539186220466882137 31829692154389665350161603)
  ·
    refine ⟨47744538231584498025242405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31829692154389665350161603 47744538231584498025242405)
    ·
      refine ⟨8952100918422093379732951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47744538231584498025242405 8952100918422093379732951)
      ·
        refine ⟨13428151377633140069599427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8952100918422093379732951 13428151377633140069599427)
        ·
          refine ⟨20142227066449710104399141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13428151377633140069599427 20142227066449710104399141)
          ·
            refine ⟨3776667574959320644574839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20142227066449710104399141 3776667574959320644574839)
            ·
              refine ⟨5665001362438980966862259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776667574959320644574839 5665001362438980966862259)
              ·
                refine ⟨8497502043658471450293389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665001362438980966862259 8497502043658471450293389)
                ·
                  refine ⟨3186563266371926793860021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8497502043658471450293389 3186563266371926793860021)
                  ·
                    refine ⟨298740306222368136924377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3186563266371926793860021 298740306222368136924377)
                    ·
                      rfl

theorem cell23_1745384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1745384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745384 prefixEnd_1745384 := by exact prefixLift 1745384
  have htrace : WordTrace (prefixWord ++ tailWord_1745384) baseStart_1745384 baseEnd_1745384 := by
    simpa [prefixWord, tailWord_1745384, baseEnd_1745384] using wordTrace_append hprefix tailTrace_1745384
  have hstable : (prefixWord ++ tailWord_1745384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745384).length < 2 ^ (prefixWord ++ tailWord_1745384).sum := by decide
  have hdescent : baseEnd_1745384 < baseStart_1745384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745415 : List Nat := [1, 1, 4, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_1745415 : Nat := 118140960795 + 1745415 * 2 ^ 59
def prefixEnd_1745415 : Nat := 4983230072969 + 3 ^ 40 * 1745415 * 2
def baseEnd_1745415 : Nat := 896236836567393789485489

theorem tailTrace_1745415 : CollatzResearch.WordTrace tailWord_1745415 prefixEnd_1745415 896236836567393789485489 := by
  unfold tailWord_1745415
  simp only [CollatzResearch.WordTrace]
  refine ⟨63660514971667022994701699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42440343314444681996467799 63660514971667022994701699)
  ·
    refine ⟨95490772457500534492052549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63660514971667022994701699 95490772457500534492052549)
    ·
      refine ⟨17904519835781350217259853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95490772457500534492052549 17904519835781350217259853)
      ·
        refine ⟨6714194938418006331472445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17904519835781350217259853 6714194938418006331472445)
        ·
          refine ⟨2517823101906752374302167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6714194938418006331472445 2517823101906752374302167)
          ·
            refine ⟨3776734652860128561453251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517823101906752374302167 3776734652860128561453251)
            ·
              refine ⟨5665101979290192842179877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776734652860128561453251 5665101979290192842179877)
              ·
                refine ⟨1062206621116911157908727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5665101979290192842179877 1062206621116911157908727)
                ·
                  refine ⟨1593309931675366736863091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062206621116911157908727 1593309931675366736863091)
                  ·
                    refine ⟨2389964897513050105294637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1593309931675366736863091 2389964897513050105294637)
                    ·
                      refine ⟨896236836567393789485489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2389964897513050105294637 896236836567393789485489)
                      ·
                        rfl

theorem cell23_1745415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_1745415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745415 prefixEnd_1745415 := by exact prefixLift 1745415
  have htrace : WordTrace (prefixWord ++ tailWord_1745415) baseStart_1745415 baseEnd_1745415 := by
    simpa [prefixWord, tailWord_1745415, baseEnd_1745415] using wordTrace_append hprefix tailTrace_1745415
  have hstable : (prefixWord ++ tailWord_1745415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745415).length < 2 ^ (prefixWord ++ tailWord_1745415).sum := by decide
  have hdescent : baseEnd_1745415 < baseStart_1745415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745417 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_1745417 : Nat := 118140960795 + 1745417 * 2 ^ 59
def prefixEnd_1745417 : Nat := 4983230072969 + 3 ^ 40 * 1745417 * 2
def baseEnd_1745417 : Nat := 896237863528702781660479

theorem tailTrace_1745417 : CollatzResearch.WordTrace tailWord_1745417 prefixEnd_1745417 896237863528702781660479 := by
  unfold tailWord_1745417
  simp only [CollatzResearch.WordTrace]
  refine ⟨63660587917659777336274505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42440391945106518224183003 63660587917659777336274505)
  ·
    refine ⟨47745440938244833002205879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63660587917659777336274505 47745440938244833002205879)
    ·
      refine ⟨71618161407367249503308819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47745440938244833002205879 71618161407367249503308819)
      ·
        refine ⟨107427242111050874254963229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71618161407367249503308819 107427242111050874254963229)
        ·
          refine ⟨40285215791644077845611211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107427242111050874254963229 40285215791644077845611211)
          ·
            refine ⟨60427823687466116768416817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40285215791644077845611211 60427823687466116768416817)
            ·
              refine ⟨45320867765599587576312613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60427823687466116768416817 45320867765599587576312613)
              ·
                refine ⟨8497662706049922670558615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45320867765599587576312613 8497662706049922670558615)
                ·
                  refine ⟨12746494059074884005837923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497662706049922670558615 12746494059074884005837923)
                  ·
                    refine ⟨19119741088612326008756885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12746494059074884005837923 19119741088612326008756885)
                    ·
                      refine ⟨896237863528702781660479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19119741088612326008756885 896237863528702781660479)
                      ·
                        rfl

theorem cell23_1745417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_1745417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745417 prefixEnd_1745417 := by exact prefixLift 1745417
  have htrace : WordTrace (prefixWord ++ tailWord_1745417) baseStart_1745417 baseEnd_1745417 := by
    simpa [prefixWord, tailWord_1745417, baseEnd_1745417] using wordTrace_append hprefix tailTrace_1745417
  have hstable : (prefixWord ++ tailWord_1745417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745417).length < 2 ^ (prefixWord ++ tailWord_1745417).sum := by decide
  have hdescent : baseEnd_1745417 < baseStart_1745417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745434 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1745434 : Nat := 118140960795 + 1745434 * 2 ^ 59
def prefixEnd_1745434 : Nat := 4983230072969 + 3 ^ 40 * 1745434 * 2
def baseEnd_1745434 : Nat := 896246592699829215147901

theorem tailTrace_1745434 : CollatzResearch.WordTrace tailWord_1745434 prefixEnd_1745434 896246592699829215147901 := by
  unfold tailWord_1745434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15915301989649547309910839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42440805305732126159762237 15915301989649547309910839)
  ·
    refine ⟨23872952984474320964866259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15915301989649547309910839 23872952984474320964866259)
    ·
      refine ⟨35809429476711481447299389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23872952984474320964866259 35809429476711481447299389)
      ·
        refine ⟨13428536053766805542737271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35809429476711481447299389 13428536053766805542737271)
        ·
          refine ⟨20142804080650208314105907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13428536053766805542737271 20142804080650208314105907)
          ·
            refine ⟨30214206120975312471158861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20142804080650208314105907 30214206120975312471158861)
            ·
              refine ⟨11330327295365742176684573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30214206120975312471158861 11330327295365742176684573)
              ·
                refine ⟨4248872735762153316256715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11330327295365742176684573 4248872735762153316256715)
                ·
                  refine ⟨6373309103643229974385073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248872735762153316256715 6373309103643229974385073)
                  ·
                    refine ⟨4779981827732422480788805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6373309103643229974385073 4779981827732422480788805)
                    ·
                      refine ⟨896246592699829215147901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4779981827732422480788805 896246592699829215147901)
                      ·
                        rfl

theorem cell23_1745434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1745434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745434 prefixEnd_1745434 := by exact prefixLift 1745434
  have htrace : WordTrace (prefixWord ++ tailWord_1745434) baseStart_1745434 baseEnd_1745434 := by
    simpa [prefixWord, tailWord_1745434, baseEnd_1745434] using wordTrace_append hprefix tailTrace_1745434
  have hstable : (prefixWord ++ tailWord_1745434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745434).length < 2 ^ (prefixWord ++ tailWord_1745434).sum := by decide
  have hdescent : baseEnd_1745434 < baseStart_1745434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745441 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1745441 : Nat := 118140960795 + 1745441 * 2 ^ 59
def prefixEnd_1745441 : Nat := 4983230072969 + 3 ^ 40 * 1745441 * 2
def baseEnd_1745441 : Nat := 896250187064410687760369

theorem tailTrace_1745441 : CollatzResearch.WordTrace tailWord_1745441 prefixEnd_1745441 896250187064410687760369 := by
  unfold tailWord_1745441
  simp only [CollatzResearch.WordTrace]
  refine ⟨63661463269572829435148177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42440975513048552956765451 63661463269572829435148177)
  ·
    refine ⟨47746097452179622076361133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63661463269572829435148177 47746097452179622076361133)
    ·
      refine ⟨17904786544567358278635425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47746097452179622076361133 17904786544567358278635425)
      ·
        refine ⟨13428589908425518708976569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17904786544567358278635425 13428589908425518708976569)
        ·
          refine ⟨10071442431319139031732427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13428589908425518708976569 10071442431319139031732427)
          ·
            refine ⟨15107163646978708547598641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10071442431319139031732427 15107163646978708547598641)
            ·
              refine ⟨11330372735234031410698981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15107163646978708547598641 11330372735234031410698981)
              ·
                refine ⟨2124444887856380889506059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11330372735234031410698981 2124444887856380889506059)
                ·
                  refine ⟨3186667331784571334259089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124444887856380889506059 3186667331784571334259089)
                  ·
                    refine ⟨2390000498838428500694317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3186667331784571334259089 2390000498838428500694317)
                    ·
                      refine ⟨896250187064410687760369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390000498838428500694317 896250187064410687760369)
                      ·
                        rfl

theorem cell23_1745441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1745441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745441 prefixEnd_1745441 := by exact prefixLift 1745441
  have htrace : WordTrace (prefixWord ++ tailWord_1745441) baseStart_1745441 baseEnd_1745441 := by
    simpa [prefixWord, tailWord_1745441, baseEnd_1745441] using wordTrace_append hprefix tailTrace_1745441
  have hstable : (prefixWord ++ tailWord_1745441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745441).length < 2 ^ (prefixWord ++ tailWord_1745441).sum := by decide
  have hdescent : baseEnd_1745441 < baseStart_1745441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745458 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_1745458 : Nat := 118140960795 + 1745458 * 2 ^ 59
def prefixEnd_1745458 : Nat := 4983230072969 + 3 ^ 40 * 1745458 * 2
def baseEnd_1745458 : Nat := 896258916235537121247791

theorem tailTrace_1745458 : CollatzResearch.WordTrace tailWord_1745458 prefixEnd_1745458 896258916235537121247791 := by
  unfold tailWord_1745458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15915520827627810334629257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42441388873674160892344685 15915520827627810334629257)
  ·
    refine ⟨11936640620720857750971943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15915520827627810334629257 11936640620720857750971943)
    ·
      refine ⟨17904960931081286626457915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936640620720857750971943 17904960931081286626457915)
      ·
        refine ⟨26857441396621929939686873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17904960931081286626457915 26857441396621929939686873)
        ·
          refine ⟨20143081047466447454765155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26857441396621929939686873 20143081047466447454765155)
          ·
            refine ⟨30214621571199671182147733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20143081047466447454765155 30214621571199671182147733)
            ·
              refine ⟨1416310386149984586663175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30214621571199671182147733 1416310386149984586663175)
              ·
                refine ⟨2124465579224976879994763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416310386149984586663175 2124465579224976879994763)
                ·
                  refine ⟨3186698368837465319992145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124465579224976879994763 3186698368837465319992145)
                  ·
                    refine ⟨2390023776628098989994109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3186698368837465319992145 2390023776628098989994109)
                    ·
                      refine ⟨896258916235537121247791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390023776628098989994109 896258916235537121247791)
                      ·
                        rfl

theorem cell23_1745458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_1745458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745458 prefixEnd_1745458 := by exact prefixLift 1745458
  have htrace : WordTrace (prefixWord ++ tailWord_1745458) baseStart_1745458 baseEnd_1745458 := by
    simpa [prefixWord, tailWord_1745458, baseEnd_1745458] using wordTrace_append hprefix tailTrace_1745458
  have hstable : (prefixWord ++ tailWord_1745458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745458).length < 2 ^ (prefixWord ++ tailWord_1745458).sum := by decide
  have hdescent : baseEnd_1745458 < baseStart_1745458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745471 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 3]
def baseStart_1745471 : Nat := 118140960795 + 1745471 * 2 ^ 59
def prefixEnd_1745471 : Nat := 4983230072969 + 3 ^ 40 * 1745471 * 2
def baseEnd_1745471 : Nat := 896265591484045570385231

theorem tailTrace_1745471 : CollatzResearch.WordTrace tailWord_1745471 prefixEnd_1745471 896265591484045570385231 := by
  unfold tailWord_1745471
  simp only [CollatzResearch.WordTrace]
  refine ⟨63662557459464144558740267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42441704972976096372493511 63662557459464144558740267)
  ·
    refine ⟨95493836189196216838110401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63662557459464144558740267 95493836189196216838110401)
    ·
      refine ⟨71620377141897162628582801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95493836189196216838110401 71620377141897162628582801)
      ·
        refine ⟨53715282856422871971437101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71620377141897162628582801 53715282856422871971437101)
        ·
          refine ⟨20143231071158576989288913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53715282856422871971437101 20143231071158576989288913)
          ·
            refine ⟨15107423303368932741966685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20143231071158576989288913 15107423303368932741966685)
            ·
              refine ⟨5665283738763349778237507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15107423303368932741966685 5665283738763349778237507)
              ·
                refine ⟨8497925608145024667356261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665283738763349778237507 8497925608145024667356261)
                ·
                  refine ⟨1593361051527192125129299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8497925608145024667356261 1593361051527192125129299)
                  ·
                    refine ⟨2390041577290788187693949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1593361051527192125129299 2390041577290788187693949)
                    ·
                      refine ⟨896265591484045570385231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390041577290788187693949 896265591484045570385231)
                      ·
                        rfl

theorem cell23_1745471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_1745471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745471 prefixEnd_1745471 := by exact prefixLift 1745471
  have htrace : WordTrace (prefixWord ++ tailWord_1745471) baseStart_1745471 baseEnd_1745471 := by
    simpa [prefixWord, tailWord_1745471, baseEnd_1745471] using wordTrace_append hprefix tailTrace_1745471
  have hstable : (prefixWord ++ tailWord_1745471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745471).length < 2 ^ (prefixWord ++ tailWord_1745471).sum := by decide
  have hdescent : baseEnd_1745471 < baseStart_1745471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745506 : List Nat := [3, 3, 2, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1745506 : Nat := 118140960795 + 1745506 * 2 ^ 59
def prefixEnd_1745506 : Nat := 4983230072969 + 3 ^ 40 * 1745506 * 2
def baseEnd_1745506 : Nat := 896283563306952933447571

theorem tailTrace_1745506 : CollatzResearch.WordTrace tailWord_1745506 prefixEnd_1745506 896283563306952933447571 := by
  unfold tailWord_1745506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15915958503584336384066093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42442556009558230357509581 15915958503584336384066093)
  ·
    refine ⟨5968484438844126144024785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15915958503584336384066093 5968484438844126144024785)
    ·
      refine ⟨4476363329133094608018589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5968484438844126144024785 4476363329133094608018589)
      ·
        refine ⟨1678636248424910478006971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4476363329133094608018589 1678636248424910478006971)
        ·
          refine ⟨2517954372637365717010457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678636248424910478006971 2517954372637365717010457)
          ·
            refine ⟨1888465779478024287757843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517954372637365717010457 1888465779478024287757843)
            ·
              refine ⟨2832698669217036431636765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888465779478024287757843 2832698669217036431636765)
              ·
                refine ⟨1062262000956388661863787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832698669217036431636765 1062262000956388661863787)
                ·
                  refine ⟨1593393001434582992795681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062262000956388661863787 1593393001434582992795681)
                  ·
                    refine ⟨1195044751075937244596761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1593393001434582992795681 1195044751075937244596761)
                    ·
                      refine ⟨896283563306952933447571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195044751075937244596761 896283563306952933447571)
                      ·
                        rfl

theorem cell23_1745506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1745506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745506 prefixEnd_1745506 := by exact prefixLift 1745506
  have htrace : WordTrace (prefixWord ++ tailWord_1745506) baseStart_1745506 baseEnd_1745506 := by
    simpa [prefixWord, tailWord_1745506, baseEnd_1745506] using wordTrace_append hprefix tailTrace_1745506
  have hstable : (prefixWord ++ tailWord_1745506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745506).length < 2 ^ (prefixWord ++ tailWord_1745506).sum := by decide
  have hdescent : baseEnd_1745506 < baseStart_1745506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745511 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_1745511 : Nat := 118140960795 + 1745511 * 2 ^ 59
def prefixEnd_1745511 : Nat := 4983230072969 + 3 ^ 40 * 1745511 * 2
def baseEnd_1745511 : Nat := 896286130710225413885047

theorem tailTrace_1745511 : CollatzResearch.WordTrace tailWord_1745511 prefixEnd_1745511 896286130710225413885047 := by
  unfold tailWord_1745511
  simp only [CollatzResearch.WordTrace]
  refine ⟨63664016379319231390196387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42442677586212820926797591 63664016379319231390196387)
  ·
    refine ⟨95496024568978847085294581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63664016379319231390196387 95496024568978847085294581)
    ·
      refine ⟨8952752303341766914246367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95496024568978847085294581 8952752303341766914246367)
      ·
        refine ⟨13429128455012650371369551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8952752303341766914246367 13429128455012650371369551)
        ·
          refine ⟨20143692682518975557054327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429128455012650371369551 20143692682518975557054327)
          ·
            refine ⟨30215539023778463335581491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20143692682518975557054327 30215539023778463335581491)
            ·
              refine ⟨45323308535667695003372237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30215539023778463335581491 45323308535667695003372237)
              ·
                refine ⟨16996240700875385626264589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45323308535667695003372237 16996240700875385626264589)
                ·
                  refine ⟨6373590262828269609849221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16996240700875385626264589 6373590262828269609849221)
                  ·
                    refine ⟨1195048174280300551846729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373590262828269609849221 1195048174280300551846729)
                    ·
                      refine ⟨896286130710225413885047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195048174280300551846729 896286130710225413885047)
                      ·
                        rfl

theorem cell23_1745511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_1745511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745511 prefixEnd_1745511 := by exact prefixLift 1745511
  have htrace : WordTrace (prefixWord ++ tailWord_1745511) baseStart_1745511 baseEnd_1745511 := by
    simpa [prefixWord, tailWord_1745511, baseEnd_1745511] using wordTrace_append hprefix tailTrace_1745511
  have hstable : (prefixWord ++ tailWord_1745511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745511).length < 2 ^ (prefixWord ++ tailWord_1745511).sum := by decide
  have hdescent : baseEnd_1745511 < baseStart_1745511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745584 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_1745584 : Nat := 118140960795 + 1745584 * 2 ^ 59
def prefixEnd_1745584 : Nat := 4983230072969 + 3 ^ 40 * 1745584 * 2
def baseEnd_1745584 : Nat := 896323614798003628272211

theorem tailTrace_1745584 : CollatzResearch.WordTrace tailWord_1745584 prefixEnd_1745584 896323614798003628272211 := by
  unfold tailWord_1745584
  simp only [CollatzResearch.WordTrace]
  refine ⟨31833339454027382428801903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42444452605369843238402537 31833339454027382428801903)
  ·
    refine ⟨47750009181041073643202855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31833339454027382428801903 47750009181041073643202855)
    ·
      refine ⟨71625013771561610464804283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47750009181041073643202855 71625013771561610464804283)
      ·
        refine ⟨107437520657342415697206425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71625013771561610464804283 107437520657342415697206425)
        ·
          refine ⟨80578140493006811772904819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107437520657342415697206425 80578140493006811772904819)
          ·
            refine ⟨120867210739510217659357229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80578140493006811772904819 120867210739510217659357229)
            ·
              refine ⟨45325204027316331622258961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120867210739510217659357229 45325204027316331622258961)
              ·
                refine ⟨33993903020487248716694221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45325204027316331622258961 33993903020487248716694221)
                ·
                  refine ⟨12747713632682718268760333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33993903020487248716694221 12747713632682718268760333)
                  ·
                    refine ⟨4780392612256019350785125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12747713632682718268760333 4780392612256019350785125)
                    ·
                      refine ⟨896323614798003628272211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4780392612256019350785125 896323614798003628272211)
                      ·
                        rfl

theorem cell23_1745584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_1745584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745584 prefixEnd_1745584 := by exact prefixLift 1745584
  have htrace : WordTrace (prefixWord ++ tailWord_1745584) baseStart_1745584 baseEnd_1745584 := by
    simpa [prefixWord, tailWord_1745584, baseEnd_1745584] using wordTrace_append hprefix tailTrace_1745584
  have hstable : (prefixWord ++ tailWord_1745584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745584).length < 2 ^ (prefixWord ++ tailWord_1745584).sum := by decide
  have hdescent : baseEnd_1745584 < baseStart_1745584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745585 : List Nat := [1, 2, 2, 6, 1, 1, 1, 4, 5]
def baseStart_1745585 : Nat := 118140960795 + 1745585 * 2 ^ 59
def prefixEnd_1745585 : Nat := 4983230072969 + 3 ^ 40 * 1745585 * 2
def baseEnd_1745585 : Nat := 99591569808739791595523

theorem tailTrace_1745585 : CollatzResearch.WordTrace tailWord_1745585 prefixEnd_1745585 99591569808739791595523 := by
  unfold tailWord_1745585
  simp only [CollatzResearch.WordTrace]
  refine ⟨63666715381051142028390209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42444476920700761352260139 63666715381051142028390209)
  ·
    refine ⟨47750036535788356521292657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63666715381051142028390209 47750036535788356521292657)
    ·
      refine ⟨35812527401841267390969493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47750036535788356521292657 35812527401841267390969493)
      ·
        refine ⟨1678712221961309408951695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35812527401841267390969493 1678712221961309408951695)
        ·
          refine ⟨2518068332941964113427543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678712221961309408951695 2518068332941964113427543)
          ·
            refine ⟨3777102499412946170141315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518068332941964113427543 3777102499412946170141315)
            ·
              refine ⟨5665653749119419255211973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777102499412946170141315 5665653749119419255211973)
              ·
                refine ⟨1062310077959891110352245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5665653749119419255211973 1062310077959891110352245)
                ·
                  refine ⟨99591569808739791595523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1062310077959891110352245 99591569808739791595523)
                  ·
                    rfl

theorem cell23_1745585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 5].length) (baseStart_1745585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745585 prefixEnd_1745585 := by exact prefixLift 1745585
  have htrace : WordTrace (prefixWord ++ tailWord_1745585) baseStart_1745585 baseEnd_1745585 := by
    simpa [prefixWord, tailWord_1745585, baseEnd_1745585] using wordTrace_append hprefix tailTrace_1745585
  have hstable : (prefixWord ++ tailWord_1745585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745585).length < 2 ^ (prefixWord ++ tailWord_1745585).sum := by decide
  have hdescent : baseEnd_1745585 < baseStart_1745585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745618 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1745618 : Nat := 118140960795 + 1745618 * 2 ^ 59
def prefixEnd_1745618 : Nat := 4983230072969 + 3 ^ 40 * 1745618 * 2
def baseEnd_1745618 : Nat := 896341073140256495247055

theorem tailTrace_1745618 : CollatzResearch.WordTrace tailWord_1745618 prefixEnd_1745618 896341073140256495247055 := by
  unfold tailWord_1745618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916979747482897166085377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42445279326621059109561005 15916979747482897166085377)
  ·
    refine ⟨11937734810612172874564033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15916979747482897166085377 11937734810612172874564033)
    ·
      refine ⟨8953301107959129655923025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11937734810612172874564033 8953301107959129655923025)
      ·
        refine ⟨6714975830969347241942269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8953301107959129655923025 6714975830969347241942269)
        ·
          refine ⟨2518115936613505215728351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6714975830969347241942269 2518115936613505215728351)
          ·
            refine ⟨3777173904920257823592527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518115936613505215728351 3777173904920257823592527)
            ·
              refine ⟨5665760857380386735388791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777173904920257823592527 5665760857380386735388791)
              ·
                refine ⟨8498641286070580103083187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665760857380386735388791 8498641286070580103083187)
                ·
                  refine ⟨12747961929105870154624781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8498641286070580103083187 12747961929105870154624781)
                  ·
                    refine ⟨4780485723414701307984293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12747961929105870154624781 4780485723414701307984293)
                    ·
                      refine ⟨896341073140256495247055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4780485723414701307984293 896341073140256495247055)
                      ·
                        rfl

theorem cell23_1745618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1745618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745618 prefixEnd_1745618 := by exact prefixLift 1745618
  have htrace : WordTrace (prefixWord ++ tailWord_1745618) baseStart_1745618 baseEnd_1745618 := by
    simpa [prefixWord, tailWord_1745618, baseEnd_1745618] using wordTrace_append hprefix tailTrace_1745618
  have hstable : (prefixWord ++ tailWord_1745618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745618).length < 2 ^ (prefixWord ++ tailWord_1745618).sum := by decide
  have hdescent : baseEnd_1745618 < baseStart_1745618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745641 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 6]
def baseStart_1745641 : Nat := 118140960795 + 1745641 * 2 ^ 59
def prefixEnd_1745641 : Nat := 4983230072969 + 3 ^ 40 * 1745641 * 2
def baseEnd_1745641 : Nat := 99594764799478878362161

theorem tailTrace_1745641 : CollatzResearch.WordTrace tailWord_1745641 prefixEnd_1745641 99594764799478878362161 := by
  unfold tailWord_1745641
  simp only [CollatzResearch.WordTrace]
  refine ⟨63668757868848263592428777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42445838579232175728285851 63668757868848263592428777)
  ·
    refine ⟨47751568401636197694321583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63668757868848263592428777 47751568401636197694321583)
    ·
      refine ⟨71627352602454296541482375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47751568401636197694321583 71627352602454296541482375)
      ·
        refine ⟨107441028903681444812223563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71627352602454296541482375 107441028903681444812223563)
        ·
          refine ⟨161161543355522167218335345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107441028903681444812223563 161161543355522167218335345)
          ·
            refine ⟨120871157516641625413751509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161161543355522167218335345 120871157516641625413751509)
            ·
              refine ⟨2832917754296288095634801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 120871157516641625413751509 2832917754296288095634801)
              ·
                refine ⟨2124688315722216071726101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832917754296288095634801 2124688315722216071726101)
                ·
                  refine ⟨99594764799478878362161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2124688315722216071726101 99594764799478878362161)
                  ·
                    rfl

theorem cell23_1745641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 6].length) (baseStart_1745641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745641 prefixEnd_1745641 := by exact prefixLift 1745641
  have htrace : WordTrace (prefixWord ++ tailWord_1745641) baseStart_1745641 baseEnd_1745641 := by
    simpa [prefixWord, tailWord_1745641, baseEnd_1745641] using wordTrace_append hprefix tailTrace_1745641
  have hstable : (prefixWord ++ tailWord_1745641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745641).length < 2 ^ (prefixWord ++ tailWord_1745641).sum := by decide
  have hdescent : baseEnd_1745641 < baseStart_1745641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745645 : List Nat := [1, 5, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_1745645 : Nat := 118140960795 + 1745645 * 2 ^ 59
def prefixEnd_1745645 : Nat := 4983230072969 + 3 ^ 40 * 1745645 * 2
def baseEnd_1745645 : Nat := 298784979039309296536477

theorem tailTrace_1745645 : CollatzResearch.WordTrace tailWord_1745645 prefixEnd_1745645 298784979039309296536477 := by
  unfold tailWord_1745645
  simp only [CollatzResearch.WordTrace]
  refine ⟨63668903760833772275574389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42445935840555848183716259 63668903760833772275574389)
  ·
    refine ⟨5968959727578166150835099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63668903760833772275574389 5968959727578166150835099)
    ·
      refine ⟨8953439591367249226252649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5968959727578166150835099 8953439591367249226252649)
      ·
        refine ⟨6715079693525436919689487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8953439591367249226252649 6715079693525436919689487)
        ·
          refine ⟨10072619540288155379534231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715079693525436919689487 10072619540288155379534231)
          ·
            refine ⟨15108929310432233069301347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10072619540288155379534231 15108929310432233069301347)
            ·
              refine ⟨22663393965648349603952021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108929310432233069301347 22663393965648349603952021)
              ·
                refine ⟨1062346592139766387685251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22663393965648349603952021 1062346592139766387685251)
                ·
                  refine ⟨1593519888209649581527877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062346592139766387685251 1593519888209649581527877)
                  ·
                    refine ⟨298784979039309296536477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1593519888209649581527877 298784979039309296536477)
                    ·
                      rfl

theorem cell23_1745645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_1745645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745645 prefixEnd_1745645 := by exact prefixLift 1745645
  have htrace : WordTrace (prefixWord ++ tailWord_1745645) baseStart_1745645 baseEnd_1745645 := by
    simpa [prefixWord, tailWord_1745645, baseEnd_1745645] using wordTrace_append hprefix tailTrace_1745645
  have hstable : (prefixWord ++ tailWord_1745645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745645).length < 2 ^ (prefixWord ++ tailWord_1745645).sum := by decide
  have hdescent : baseEnd_1745645 < baseStart_1745645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745695 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 2, 3, 2]
def baseStart_1745695 : Nat := 118140960795 + 1745695 * 2 ^ 59
def prefixEnd_1745695 : Nat := 4983230072969 + 3 ^ 40 * 1745695 * 2
def baseEnd_1745695 : Nat := 896380611150652693984201

theorem tailTrace_1745695 : CollatzResearch.WordTrace tailWord_1745695 prefixEnd_1745695 896380611150652693984201 := by
  unfold tailWord_1745695
  simp only [CollatzResearch.WordTrace]
  refine ⟨63670727410652630814894539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42447151607101753876596359 63670727410652630814894539)
  ·
    refine ⟨95506091115978946222341809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63670727410652630814894539 95506091115978946222341809)
    ·
      refine ⟨71629568336984209666756357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95506091115978946222341809 71629568336984209666756357)
      ·
        refine ⟨13430544063184539312516817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71629568336984209666756357 13430544063184539312516817)
        ·
          refine ⟨10072908047388404484387613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13430544063184539312516817 10072908047388404484387613)
          ·
            refine ⟨3777340517770651681645355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10072908047388404484387613 3777340517770651681645355)
            ·
              refine ⟨5666010776655977522468033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777340517770651681645355 5666010776655977522468033)
              ·
                refine ⟨4249508082491983141851025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5666010776655977522468033 4249508082491983141851025)
                ·
                  refine ⟨3187131061868987356388269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4249508082491983141851025 3187131061868987356388269)
                  ·
                    refine ⟨1195174148200870258645601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187131061868987356388269 1195174148200870258645601)
                    ·
                      refine ⟨896380611150652693984201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195174148200870258645601 896380611150652693984201)
                      ·
                        rfl

theorem cell23_1745695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_1745695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745695 prefixEnd_1745695 := by exact prefixLift 1745695
  have htrace : WordTrace (prefixWord ++ tailWord_1745695) baseStart_1745695 baseEnd_1745695 := by
    simpa [prefixWord, tailWord_1745695, baseEnd_1745695] using wordTrace_append hprefix tailTrace_1745695
  have hstable : (prefixWord ++ tailWord_1745695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745695).length < 2 ^ (prefixWord ++ tailWord_1745695).sum := by decide
  have hdescent : baseEnd_1745695 < baseStart_1745695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745709 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 6]
def baseStart_1745709 : Nat := 118140960795 + 1745709 * 2 ^ 59
def prefixEnd_1745709 : Nat := 4983230072969 + 3 ^ 40 * 1745709 * 2
def baseEnd_1745709 : Nat := 99598644431090626578793

theorem tailTrace_1745709 : CollatzResearch.WordTrace tailWord_1745709 prefixEnd_1745709 99598644431090626578793 := by
  unfold tailWord_1745709
  simp only [CollatzResearch.WordTrace]
  refine ⟨63671238032601911205904181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42447492021734607470602787 63671238032601911205904181)
  ·
    refine ⟨5969178565556429175553517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63671238032601911205904181 5969178565556429175553517)
    ·
      refine ⟨2238441962083660940832569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5969178565556429175553517 2238441962083660940832569)
      ·
        refine ⟨1678831471562745705624427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2238441962083660940832569 1678831471562745705624427)
        ·
          refine ⟨2518247207344118558436641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678831471562745705624427 2518247207344118558436641)
          ·
            refine ⟨1888685405508088918827481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518247207344118558436641 1888685405508088918827481)
            ·
              refine ⟨1416514054131066689120611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888685405508088918827481 1416514054131066689120611)
              ·
                refine ⟨2124771081196600033680917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416514054131066689120611 2124771081196600033680917)
                ·
                  refine ⟨99598644431090626578793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2124771081196600033680917 99598644431090626578793)
                  ·
                    rfl

theorem cell23_1745709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_1745709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745709 prefixEnd_1745709 := by exact prefixLift 1745709
  have htrace : WordTrace (prefixWord ++ tailWord_1745709) baseStart_1745709 baseEnd_1745709 := by
    simpa [prefixWord, tailWord_1745709, baseEnd_1745709] using wordTrace_append hprefix tailTrace_1745709
  have hstable : (prefixWord ++ tailWord_1745709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745709).length < 2 ^ (prefixWord ++ tailWord_1745709).sum := by decide
  have hdescent : baseEnd_1745709 < baseStart_1745709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745722 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_1745722 : Nat := 118140960795 + 1745722 * 2 ^ 59
def prefixEnd_1745722 : Nat := 4983230072969 + 3 ^ 40 * 1745722 * 2
def baseEnd_1745722 : Nat := 298798158376108029448859

theorem tailTrace_1745722 : CollatzResearch.WordTrace tailWord_1745722 prefixEnd_1745722 298798158376108029448859 := by
  unfold tailWord_1745722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15917928045388703606531855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42447808121036542950751613 15917928045388703606531855)
  ·
    refine ⟨23876892068083055409797783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15917928045388703606531855 23876892068083055409797783)
    ·
      refine ⟨35815338102124583114696675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23876892068083055409797783 35815338102124583114696675)
      ·
        refine ⟨53723007153186874672045013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35815338102124583114696675 53723007153186874672045013)
        ·
          refine ⟨1259132980152817375126055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 53723007153186874672045013 1259132980152817375126055)
          ·
            refine ⟨1888699470229226062689083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259132980152817375126055 1888699470229226062689083)
            ·
              refine ⟨2833049205343839094033625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888699470229226062689083 2833049205343839094033625)
              ·
                refine ⟨2124786904007879320525219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833049205343839094033625 2124786904007879320525219)
                ·
                  refine ⟨3187180356011818980787829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124786904007879320525219 3187180356011818980787829)
                  ·
                    refine ⟨298798158376108029448859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3187180356011818980787829 298798158376108029448859)
                    ·
                      rfl

theorem cell23_1745722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_1745722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745722 prefixEnd_1745722 := by exact prefixLift 1745722
  have htrace : WordTrace (prefixWord ++ tailWord_1745722) baseStart_1745722 baseEnd_1745722 := by
    simpa [prefixWord, tailWord_1745722, baseEnd_1745722] using wordTrace_append hprefix tailTrace_1745722
  have hstable : (prefixWord ++ tailWord_1745722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745722).length < 2 ^ (prefixWord ++ tailWord_1745722).sum := by decide
  have hdescent : baseEnd_1745722 < baseStart_1745722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745725 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1745725 : Nat := 118140960795 + 1745725 * 2 ^ 59
def prefixEnd_1745725 : Nat := 4983230072969 + 3 ^ 40 * 1745725 * 2
def baseEnd_1745725 : Nat := 896396015570287576609063

theorem tailTrace_1745725 : CollatzResearch.WordTrace tailWord_1745725 prefixEnd_1745725 896396015570287576609063 := by
  unfold tailWord_1745725
  simp only [CollatzResearch.WordTrace]
  refine ⟨63671821600543945938486629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42447881067029297292324419 63671821600543945938486629)
  ·
    refine ⟨11938466550101989863466243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63671821600543945938486629 11938466550101989863466243)
    ·
      refine ⟨17907699825152984795199365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11938466550101989863466243 17907699825152984795199365)
      ·
        refine ⟨3357693717216184649099881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17907699825152984795199365 3357693717216184649099881)
        ·
          refine ⟨2518270287912138486824911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3357693717216184649099881 2518270287912138486824911)
          ·
            refine ⟨3777405431868207730237367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518270287912138486824911 3777405431868207730237367)
            ·
              refine ⟨5666108147802311595356051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777405431868207730237367 5666108147802311595356051)
              ·
                refine ⟨8499162221703467393034077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666108147802311595356051 8499162221703467393034077)
                ·
                  refine ⟨3187185833138800272387779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8499162221703467393034077 3187185833138800272387779)
                  ·
                    refine ⟨4780778749708200408581669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3187185833138800272387779 4780778749708200408581669)
                    ·
                      refine ⟨896396015570287576609063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4780778749708200408581669 896396015570287576609063)
                      ·
                        rfl

theorem cell23_1745725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1745725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745725 prefixEnd_1745725 := by exact prefixLift 1745725
  have htrace : WordTrace (prefixWord ++ tailWord_1745725) baseStart_1745725 baseEnd_1745725 := by
    simpa [prefixWord, tailWord_1745725, baseEnd_1745725] using wordTrace_append hprefix tailTrace_1745725
  have hstable : (prefixWord ++ tailWord_1745725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745725).length < 2 ^ (prefixWord ++ tailWord_1745725).sum := by decide
  have hdescent : baseEnd_1745725 < baseStart_1745725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745729 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1745729 : Nat := 118140960795 + 1745729 * 2 ^ 59
def prefixEnd_1745729 : Nat := 4983230072969 + 3 ^ 40 * 1745729 * 2
def baseEnd_1745729 : Nat := 896398069492905560959045

theorem tailTrace_1745729 : CollatzResearch.WordTrace tailWord_1745729 prefixEnd_1745729 896398069492905560959045 := by
  unfold tailWord_1745729
  simp only [CollatzResearch.WordTrace]
  refine ⟨63671967492529454621632241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42447978328352969747754827 63671967492529454621632241)
  ·
    refine ⟨47753975619397090966224181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63671967492529454621632241 47753975619397090966224181)
    ·
      refine ⟨4476935214318477278083517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47753975619397090966224181 4476935214318477278083517)
      ·
        refine ⟨1678850705369428979281319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4476935214318477278083517 1678850705369428979281319)
        ·
          refine ⟨2518276058054143468921979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678850705369428979281319 2518276058054143468921979)
          ·
            refine ⟨3777414087081215203382969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518276058054143468921979 3777414087081215203382969)
            ·
              refine ⟨2833060565310911402537227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777414087081215203382969 2833060565310911402537227)
              ·
                refine ⟨4249590847966367103805841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833060565310911402537227 4249590847966367103805841)
                ·
                  refine ⟨3187193135974775327854381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4249590847966367103805841 3187193135974775327854381)
                  ·
                    refine ⟨1195197425990540747945393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187193135974775327854381 1195197425990540747945393)
                    ·
                      refine ⟨896398069492905560959045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195197425990540747945393 896398069492905560959045)
                      ·
                        rfl

theorem cell23_1745729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1745729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745729 prefixEnd_1745729 := by exact prefixLift 1745729
  have htrace : WordTrace (prefixWord ++ tailWord_1745729) baseStart_1745729 baseEnd_1745729 := by
    simpa [prefixWord, tailWord_1745729, baseEnd_1745729] using wordTrace_append hprefix tailTrace_1745729
  have hstable : (prefixWord ++ tailWord_1745729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745729).length < 2 ^ (prefixWord ++ tailWord_1745729).sum := by decide
  have hdescent : baseEnd_1745729 < baseStart_1745729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745745 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_1745745 : Nat := 118140960795 + 1745745 * 2 ^ 59
def prefixEnd_1745745 : Nat := 4983230072969 + 3 ^ 40 * 1745745 * 2
def baseEnd_1745745 : Nat := 896406285183377498358971

theorem tailTrace_1745745 : CollatzResearch.WordTrace tailWord_1745745 prefixEnd_1745745 896406285183377498358971 := by
  unfold tailWord_1745745
  simp only [CollatzResearch.WordTrace]
  refine ⟨63672551060471489354214689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42448367373647659569476459 63672551060471489354214689)
  ·
    refine ⟨47754413295353617015661017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63672551060471489354214689 47754413295353617015661017)
    ·
      refine ⟨35815809971515212761745763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47754413295353617015661017 35815809971515212761745763)
      ·
        refine ⟨53723714957272819142618645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35815809971515212761745763 53723714957272819142618645)
        ·
          refine ⟨2518299138622163397310249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53723714957272819142618645 2518299138622163397310249)
          ·
            refine ⟨1888724353966622547982687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518299138622163397310249 1888724353966622547982687)
            ·
              refine ⟨2833086530949933821974031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888724353966622547982687 2833086530949933821974031)
              ·
                refine ⟨4249629796424900732961047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833086530949933821974031 4249629796424900732961047)
                ·
                  refine ⟨6374444694637351099441571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249629796424900732961047 6374444694637351099441571)
                  ·
                    refine ⟨9561667041956026649162357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6374444694637351099441571 9561667041956026649162357)
                    ·
                      refine ⟨896406285183377498358971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9561667041956026649162357 896406285183377498358971)
                      ·
                        rfl

theorem cell23_1745745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_1745745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745745 prefixEnd_1745745 := by exact prefixLift 1745745
  have htrace : WordTrace (prefixWord ++ tailWord_1745745) baseStart_1745745 baseEnd_1745745 := by
    simpa [prefixWord, tailWord_1745745, baseEnd_1745745] using wordTrace_append hprefix tailTrace_1745745
  have hstable : (prefixWord ++ tailWord_1745745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745745).length < 2 ^ (prefixWord ++ tailWord_1745745).sum := by decide
  have hdescent : baseEnd_1745745 < baseStart_1745745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745748 : List Nat := [2, 4, 1, 1, 5, 10]
def baseStart_1745748 : Nat := 118140960795 + 1745748 * 2 ^ 59
def prefixEnd_1745748 : Nat := 4983230072969 + 3 ^ 40 * 1745748 * 2
def baseEnd_1745748 : Nat := 3688921093108399121899

theorem tailTrace_1745748 : CollatzResearch.WordTrace tailWord_1745748 prefixEnd_1745748 3688921093108399121899 := by
  unfold tailWord_1745748
  simp only [CollatzResearch.WordTrace]
  refine ⟨31836330239730310433286949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42448440319640413911049265 31836330239730310433286949)
  ·
    refine ⟨5969311919949433206241303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31836330239730310433286949 5969311919949433206241303)
    ·
      refine ⟨8953967879924149809361955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969311919949433206241303 8953967879924149809361955)
      ·
        refine ⟨13430951819886224714042933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8953967879924149809361955 13430951819886224714042933)
        ·
          refine ⟨1259151733114333566941525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13430951819886224714042933 1259151733114333566941525)
          ·
            refine ⟨3688921093108399121899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1259151733114333566941525 3688921093108399121899)
            ·
              rfl

theorem cell23_1745748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 10].length) (baseStart_1745748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745748 prefixEnd_1745748 := by exact prefixLift 1745748
  have htrace : WordTrace (prefixWord ++ tailWord_1745748) baseStart_1745748 baseEnd_1745748 := by
    simpa [prefixWord, tailWord_1745748, baseEnd_1745748] using wordTrace_append hprefix tailTrace_1745748
  have hstable : (prefixWord ++ tailWord_1745748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745748).length < 2 ^ (prefixWord ++ tailWord_1745748).sum := by decide
  have hdescent : baseEnd_1745748 < baseStart_1745748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745785 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 3, 3, 2]
def baseStart_1745785 : Nat := 118140960795 + 1745785 * 2 ^ 59
def prefixEnd_1745785 : Nat := 4983230072969 + 3 ^ 40 * 1745785 * 2
def baseEnd_1745785 : Nat := 896426824409557341858787

theorem tailTrace_1745785 : CollatzResearch.WordTrace tailWord_1745785 prefixEnd_1745785 896426824409557341858787 := by
  unfold tailWord_1745785
  simp only [CollatzResearch.WordTrace]
  refine ⟨63674009980326576185670809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42449339986884384123780539 63674009980326576185670809)
  ·
    refine ⟨47755507485244932139253107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63674009980326576185670809 47755507485244932139253107)
    ·
      refine ⟨71633261227867398208879661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47755507485244932139253107 71633261227867398208879661)
      ·
        refine ⟨26862472960450274328329873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71633261227867398208879661 26862472960450274328329873)
        ·
          refine ⟨20146854720337705746247405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26862472960450274328329873 20146854720337705746247405)
          ·
            refine ⟨7555070520126639654842777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20146854720337705746247405 7555070520126639654842777)
            ·
              refine ⟨5666302890094979741132083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7555070520126639654842777 5666302890094979741132083)
              ·
                refine ⟨8499454335142469611698125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666302890094979741132083 8499454335142469611698125)
                ·
                  refine ⟨3187295375678426104386797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8499454335142469611698125 3187295375678426104386797)
                  ·
                    refine ⟨1195235765879409789145049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3187295375678426104386797 1195235765879409789145049)
                    ·
                      refine ⟨896426824409557341858787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195235765879409789145049 896426824409557341858787)
                      ·
                        rfl

theorem cell23_1745785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_1745785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745785 prefixEnd_1745785 := by exact prefixLift 1745785
  have htrace : WordTrace (prefixWord ++ tailWord_1745785) baseStart_1745785 baseEnd_1745785 := by
    simpa [prefixWord, tailWord_1745785, baseEnd_1745785] using wordTrace_append hprefix tailTrace_1745785
  have hstable : (prefixWord ++ tailWord_1745785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745785).length < 2 ^ (prefixWord ++ tailWord_1745785).sum := by decide
  have hdescent : baseEnd_1745785 < baseStart_1745785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745828 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1745828 : Nat := 118140960795 + 1745828 * 2 ^ 59
def prefixEnd_1745828 : Nat := 4983230072969 + 3 ^ 40 * 1745828 * 2
def baseEnd_1745828 : Nat := 896448904077700673621089

theorem tailTrace_1745828 : CollatzResearch.WordTrace tailWord_1745828 prefixEnd_1745828 896448904077700673621089 := by
  unfold tailWord_1745828
  simp only [CollatzResearch.WordTrace]
  refine ⟨31837789159585397264743069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42450385546113863019657425 31837789159585397264743069)
  ·
    refine ⟨11939170934844523974278651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31837789159585397264743069 11939170934844523974278651)
    ·
      refine ⟨17908756402266785961417977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11939170934844523974278651 17908756402266785961417977)
      ·
        refine ⟨13431567301700089471063483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17908756402266785961417977 13431567301700089471063483)
        ·
          refine ⟨20147350952550134206595225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13431567301700089471063483 20147350952550134206595225)
          ·
            refine ⟨15110513214412600654946419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20147350952550134206595225 15110513214412600654946419)
            ·
              refine ⟨22665769821618900982419629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15110513214412600654946419 22665769821618900982419629)
              ·
                refine ⟨8499663683107087868407361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22665769821618900982419629 8499663683107087868407361)
                ·
                  refine ⟨6374747762330315901305521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8499663683107087868407361 6374747762330315901305521)
                  ·
                    refine ⟨4781060821747736925979141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6374747762330315901305521 4781060821747736925979141)
                    ·
                      refine ⟨896448904077700673621089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4781060821747736925979141 896448904077700673621089)
                      ·
                        rfl

theorem cell23_1745828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1745828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745828 prefixEnd_1745828 := by exact prefixLift 1745828
  have htrace : WordTrace (prefixWord ++ tailWord_1745828) baseStart_1745828 baseEnd_1745828 := by
    simpa [prefixWord, tailWord_1745828, baseEnd_1745828] using wordTrace_append hprefix tailTrace_1745828
  have hstable : (prefixWord ++ tailWord_1745828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745828).length < 2 ^ (prefixWord ++ tailWord_1745828).sum := by decide
  have hdescent : baseEnd_1745828 < baseStart_1745828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745851 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 5, 7]
def baseStart_1745851 : Nat := 118140960795 + 1745851 * 2 ^ 59
def prefixEnd_1745851 : Nat := 4983230072969 + 3 ^ 40 * 1745851 * 2
def baseEnd_1745851 : Nat := 298820238044251361211161

theorem tailTrace_1745851 : CollatzResearch.WordTrace tailWord_1745851 prefixEnd_1745851 298820238044251361211161 := by
  unfold tailWord_1745851
  simp only [CollatzResearch.WordTrace]
  refine ⟨63676417198087469457573407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42450944798724979638382271 63676417198087469457573407)
  ·
    refine ⟨95514625797131204186360111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63676417198087469457573407 95514625797131204186360111)
    ·
      refine ⟨143271938695696806279540167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95514625797131204186360111 143271938695696806279540167)
      ·
        refine ⟨214907908043545209419310251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143271938695696806279540167 214907908043545209419310251)
        ·
          refine ⟨322361862065317814128965377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214907908043545209419310251 322361862065317814128965377)
          ·
            refine ⟨241771396548988360596724033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322361862065317814128965377 241771396548988360596724033)
            ·
              refine ⟨181328547411741270447543025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241771396548988360596724033 181328547411741270447543025)
              ·
                refine ⟨135996410558805952835657269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181328547411741270447543025 135996410558805952835657269)
                ·
                  refine ⟨12749663489888058078342869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135996410558805952835657269 12749663489888058078342869)
                  ·
                    refine ⟨298820238044251361211161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12749663489888058078342869 298820238044251361211161)
                    ·
                      rfl

theorem cell23_1745851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_1745851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745851 prefixEnd_1745851 := by exact prefixLift 1745851
  have htrace : WordTrace (prefixWord ++ tailWord_1745851) baseStart_1745851 baseEnd_1745851 := by
    simpa [prefixWord, tailWord_1745851, baseEnd_1745851] using wordTrace_append hprefix tailTrace_1745851
  have hstable : (prefixWord ++ tailWord_1745851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745851).length < 2 ^ (prefixWord ++ tailWord_1745851).sum := by decide
  have hdescent : baseEnd_1745851 < baseStart_1745851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745902 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1745902 : Nat := 118140960795 + 1745902 * 2 ^ 59
def prefixEnd_1745902 : Nat := 4983230072969 + 3 ^ 40 * 1745902 * 2
def baseEnd_1745902 : Nat := 298828967215377794698583

theorem tailTrace_1745902 : CollatzResearch.WordTrace tailWord_1745902 prefixEnd_1745902 298828967215377794698583 := by
  unfold tailWord_1745902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959784665112838145959995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42452184880601803445119973 7959784665112838145959995)
  ·
    refine ⟨11939676997669257218939993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7959784665112838145959995 11939676997669257218939993)
    ·
      refine ⟨8954757748251942914204995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11939676997669257218939993 8954757748251942914204995)
      ·
        refine ⟨13432136622377914371307493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8954757748251942914204995 13432136622377914371307493)
        ·
          refine ⟨2518525616695858944620155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13432136622377914371307493 2518525616695858944620155)
          ·
            refine ⟨3777788425043788416930233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518525616695858944620155 3777788425043788416930233)
            ·
              refine ⟨2833341318782841312697675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777788425043788416930233 2833341318782841312697675)
              ·
                refine ⟨4250011978174261969046513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833341318782841312697675 4250011978174261969046513)
                ·
                  refine ⟨3187508983630696476784885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4250011978174261969046513 3187508983630696476784885)
                  ·
                    refine ⟨298828967215377794698583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3187508983630696476784885 298828967215377794698583)
                    ·
                      rfl

theorem cell23_1745902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1745902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745902 prefixEnd_1745902 := by exact prefixLift 1745902
  have htrace : WordTrace (prefixWord ++ tailWord_1745902) baseStart_1745902 baseEnd_1745902 := by
    simpa [prefixWord, tailWord_1745902, baseEnd_1745902] using wordTrace_append hprefix tailTrace_1745902
  have hstable : (prefixWord ++ tailWord_1745902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745902).length < 2 ^ (prefixWord ++ tailWord_1745902).sum := by decide
  have hdescent : baseEnd_1745902 < baseStart_1745902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745905 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_1745905 : Nat := 118140960795 + 1745905 * 2 ^ 59
def prefixEnd_1745905 : Nat := 4983230072969 + 3 ^ 40 * 1745905 * 2
def baseEnd_1745905 : Nat := 896488442088096872358235

theorem tailTrace_1745905 : CollatzResearch.WordTrace tailWord_1745905 prefixEnd_1745905 896488442088096872358235 := by
  unfold tailWord_1745905
  simp only [CollatzResearch.WordTrace]
  refine ⟨63678386739891836680039169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42452257826594557786692779 63678386739891836680039169)
  ·
    refine ⟨47758790054918877510029377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63678386739891836680039169 47758790054918877510029377)
    ·
      refine ⟨35819092541189158132522033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47758790054918877510029377 35819092541189158132522033)
      ·
        refine ⟨26864319405891868599391525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35819092541189158132522033 26864319405891868599391525)
        ·
          refine ⟨5037059888604725362385911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26864319405891868599391525 5037059888604725362385911)
          ·
            refine ⟨7555589832907088043578867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037059888604725362385911 7555589832907088043578867)
            ·
              refine ⟨11333384749360632065368301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555589832907088043578867 11333384749360632065368301)
              ·
                refine ⟨4250019281010237024513113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11333384749360632065368301 4250019281010237024513113)
                ·
                  refine ⟨3187514460757677768384835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4250019281010237024513113 3187514460757677768384835)
                  ·
                    refine ⟨4781271691136516652577253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3187514460757677768384835 4781271691136516652577253)
                    ·
                      refine ⟨896488442088096872358235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4781271691136516652577253 896488442088096872358235)
                      ·
                        rfl

theorem cell23_1745905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_1745905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745905 prefixEnd_1745905 := by exact prefixLift 1745905
  have htrace : WordTrace (prefixWord ++ tailWord_1745905) baseStart_1745905 baseEnd_1745905 := by
    simpa [prefixWord, tailWord_1745905, baseEnd_1745905] using wordTrace_append hprefix tailTrace_1745905
  have hstable : (prefixWord ++ tailWord_1745905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745905).length < 2 ^ (prefixWord ++ tailWord_1745905).sum := by decide
  have hdescent : baseEnd_1745905 < baseStart_1745905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745925 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_1745925 : Nat := 118140960795 + 1745925 * 2 ^ 59
def prefixEnd_1745925 : Nat := 4983230072969 + 3 ^ 40 * 1745925 * 2
def baseEnd_1745925 : Nat := 896498711701186794108143

theorem tailTrace_1745925 : CollatzResearch.WordTrace tailWord_1745925 prefixEnd_1745925 896498711701186794108143 := by
  unfold tailWord_1745925
  simp only [CollatzResearch.WordTrace]
  refine ⟨63679116199819380095767229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42452744133212920063844819 63679116199819380095767229)
  ·
    refine ⟨23879668574932267535912711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63679116199819380095767229 23879668574932267535912711)
    ·
      refine ⟨35819502862398401303869067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23879668574932267535912711 35819502862398401303869067)
      ·
        refine ⟨53729254293597601955803601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35819502862398401303869067 53729254293597601955803601)
        ·
          refine ⟨40296940720198201466852701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53729254293597601955803601 40296940720198201466852701)
          ·
            refine ⟨15111352770074325550069763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40296940720198201466852701 15111352770074325550069763)
            ·
              refine ⟨22667029155111488325104645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15111352770074325550069763 22667029155111488325104645)
              ·
                refine ⟨4250067966583404060957121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22667029155111488325104645 4250067966583404060957121)
                ·
                  refine ⟨3187550974937553045717841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4250067966583404060957121 3187550974937553045717841)
                  ·
                    refine ⟨2390663231203164784288381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3187550974937553045717841 2390663231203164784288381)
                    ·
                      refine ⟨896498711701186794108143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390663231203164784288381 896498711701186794108143)
                      ·
                        rfl

theorem cell23_1745925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_1745925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745925 prefixEnd_1745925 := by exact prefixLift 1745925
  have htrace : WordTrace (prefixWord ++ tailWord_1745925) baseStart_1745925 baseEnd_1745925 := by
    simpa [prefixWord, tailWord_1745925, baseEnd_1745925] using wordTrace_append hprefix tailTrace_1745925
  have hstable : (prefixWord ++ tailWord_1745925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745925).length < 2 ^ (prefixWord ++ tailWord_1745925).sum := by decide
  have hdescent : baseEnd_1745925 < baseStart_1745925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745959 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1745959 : Nat := 118140960795 + 1745959 * 2 ^ 59
def prefixEnd_1745959 : Nat := 4983230072969 + 3 ^ 40 * 1745959 * 2
def baseEnd_1745959 : Nat := 896516170043439661082987

theorem tailTrace_1745959 : CollatzResearch.WordTrace tailWord_1745959 prefixEnd_1745959 896516170043439661082987 := by
  unfold tailWord_1745959
  simp only [CollatzResearch.WordTrace]
  refine ⟨63680356281696203902504931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42453570854464135935003287 63680356281696203902504931)
  ·
    refine ⟨95520534422544305853757397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63680356281696203902504931 95520534422544305853757397)
    ·
      refine ⟨2238762525528382168447439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95520534422544305853757397 2238762525528382168447439)
      ·
        refine ⟨3358143788292573252671159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238762525528382168447439 3358143788292573252671159)
        ·
          refine ⟨5037215682438859879006739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358143788292573252671159 5037215682438859879006739)
          ·
            refine ⟨7555823523658289818510109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037215682438859879006739 7555823523658289818510109)
            ·
              refine ⟨2833433821371858681941291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7555823523658289818510109 2833433821371858681941291)
              ·
                refine ⟨4250150732057788022911937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833433821371858681941291 4250150732057788022911937)
                ·
                  refine ⟨3187613049043341017183953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4250150732057788022911937 3187613049043341017183953)
                  ·
                    refine ⟨2390709786782505762887965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3187613049043341017183953 2390709786782505762887965)
                    ·
                      refine ⟨896516170043439661082987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390709786782505762887965 896516170043439661082987)
                      ·
                        rfl

theorem cell23_1745959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1745959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745959 prefixEnd_1745959 := by exact prefixLift 1745959
  have htrace : WordTrace (prefixWord ++ tailWord_1745959) baseStart_1745959 baseEnd_1745959 := by
    simpa [prefixWord, tailWord_1745959, baseEnd_1745959] using wordTrace_append hprefix tailTrace_1745959
  have hstable : (prefixWord ++ tailWord_1745959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745959).length < 2 ^ (prefixWord ++ tailWord_1745959).sum := by decide
  have hdescent : baseEnd_1745959 < baseStart_1745959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745989 : List Nat := [1, 3, 1, 1, 1, 3, 4, 4, 1, 1, 3]
def baseStart_1745989 : Nat := 118140960795 + 1745989 * 2 ^ 59
def prefixEnd_1745989 : Nat := 4983230072969 + 3 ^ 40 * 1745989 * 2
def baseEnd_1745989 : Nat := 896531574463074543707849

theorem tailTrace_1745989 : CollatzResearch.WordTrace tailWord_1745989 prefixEnd_1745989 896531574463074543707849 := by
  unfold tailWord_1745989
  simp only [CollatzResearch.WordTrace]
  refine ⟨63681450471587519026097021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42454300314391679350731347 63681450471587519026097021)
  ·
    refine ⟨23880543926845319634786383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63681450471587519026097021 23880543926845319634786383)
    ·
      refine ⟨35820815890267979452179575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23880543926845319634786383 35820815890267979452179575)
      ·
        refine ⟨53731223835401969178269363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35820815890267979452179575 53731223835401969178269363)
        ·
          refine ⟨80596835753102953767404045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53731223835401969178269363 80596835753102953767404045)
          ·
            refine ⟨30223813407413607662776517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80596835753102953767404045 30223813407413607662776517)
            ·
              refine ⟨5666965013890051436770597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30223813407413607662776517 5666965013890051436770597)
              ·
                refine ⟨1062555940104384644394487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5666965013890051436770597 1062555940104384644394487)
                ·
                  refine ⟨1593833910156576966591731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062555940104384644394487 1593833910156576966591731)
                  ·
                    refine ⟨2390750865234865449887597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1593833910156576966591731 2390750865234865449887597)
                    ·
                      refine ⟨896531574463074543707849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390750865234865449887597 896531574463074543707849)
                      ·
                        rfl

theorem cell23_1745989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_1745989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745989 prefixEnd_1745989 := by exact prefixLift 1745989
  have htrace : WordTrace (prefixWord ++ tailWord_1745989) baseStart_1745989 baseEnd_1745989 := by
    simpa [prefixWord, tailWord_1745989, baseEnd_1745989] using wordTrace_append hprefix tailTrace_1745989
  have hstable : (prefixWord ++ tailWord_1745989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745989).length < 2 ^ (prefixWord ++ tailWord_1745989).sum := by decide
  have hdescent : baseEnd_1745989 < baseStart_1745989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745995 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 4, 6, 2]
def baseStart_1745995 : Nat := 118140960795 + 1745995 * 2 ^ 59
def prefixEnd_1745995 : Nat := 4983230072969 + 3 ^ 40 * 1745995 * 2
def baseEnd_1745995 : Nat := 896534655347001520232821

theorem tailTrace_1745995 : CollatzResearch.WordTrace tailWord_1745995 prefixEnd_1745995 896534655347001520232821 := by
  unfold tailWord_1745995
  simp only [CollatzResearch.WordTrace]
  refine ⟨63681669309565782050815439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42454446206377188033876959 63681669309565782050815439)
  ·
    refine ⟨95522503964348673076223159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63681669309565782050815439 95522503964348673076223159)
    ·
      refine ⟨143283755946523009614334739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95522503964348673076223159 143283755946523009614334739)
      ·
        refine ⟨214925633919784514421502109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143283755946523009614334739 214925633919784514421502109)
        ·
          refine ⟨80597112719919192908063291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214925633919784514421502109 80597112719919192908063291)
          ·
            refine ⟨120895669079878789362094937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80597112719919192908063291 120895669079878789362094937)
            ·
              refine ⟨90671751809909092021571203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120895669079878789362094937 90671751809909092021571203)
              ·
                refine ⟨136007627714863638032356805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90671751809909092021571203 136007627714863638032356805)
                ·
                  refine ⟨25501430196536932131066901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136007627714863638032356805 25501430196536932131066901)
                  ·
                    refine ⟨1195379540462668693643761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25501430196536932131066901 1195379540462668693643761)
                    ·
                      refine ⟨896534655347001520232821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195379540462668693643761 896534655347001520232821)
                      ·
                        rfl

theorem cell23_1745995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6, 2].length) (baseStart_1745995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745995 prefixEnd_1745995 := by exact prefixLift 1745995
  have htrace : WordTrace (prefixWord ++ tailWord_1745995) baseStart_1745995 baseEnd_1745995 := by
    simpa [prefixWord, tailWord_1745995, baseEnd_1745995] using wordTrace_append hprefix tailTrace_1745995
  have hstable : (prefixWord ++ tailWord_1745995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745995).length < 2 ^ (prefixWord ++ tailWord_1745995).sum := by decide
  have hdescent : baseEnd_1745995 < baseStart_1745995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746012 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_1746012 : Nat := 118140960795 + 1746012 * 2 ^ 59
def prefixEnd_1746012 : Nat := 4983230072969 + 3 ^ 40 * 1746012 * 2
def baseEnd_1746012 : Nat := 896543384518127953720243

theorem tailTrace_1746012 : CollatzResearch.WordTrace tailWord_1746012 prefixEnd_1746012 896543384518127953720243 := by
  unfold tailWord_1746012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31841144675252096977092145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42454859567002795969456193 31841144675252096977092145)
  ·
    refine ⟨23880858506439072732819109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31841144675252096977092145 23880858506439072732819109)
    ·
      refine ⟨4477660969957326137403583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23880858506439072732819109 4477660969957326137403583)
      ·
        refine ⟨6716491454935989206105375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477660969957326137403583 6716491454935989206105375)
        ·
          refine ⟨10074737182403983809158063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716491454935989206105375 10074737182403983809158063)
          ·
            refine ⟨15112105773605975713737095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10074737182403983809158063 15112105773605975713737095)
            ·
              refine ⟨22668158660408963570605643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15112105773605975713737095 22668158660408963570605643)
              ·
                refine ⟨34002237990613445355908465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22668158660408963570605643 34002237990613445355908465)
                ·
                  refine ⟨25501678492960084016931349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34002237990613445355908465 25501678492960084016931349)
                  ·
                    refine ⟨1195391179357503938293657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25501678492960084016931349 1195391179357503938293657)
                    ·
                      refine ⟨896543384518127953720243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195391179357503938293657 896543384518127953720243)
                      ·
                        rfl

theorem cell23_1746012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_1746012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746012 prefixEnd_1746012 := by exact prefixLift 1746012
  have htrace : WordTrace (prefixWord ++ tailWord_1746012) baseStart_1746012 baseEnd_1746012 := by
    simpa [prefixWord, tailWord_1746012, baseEnd_1746012] using wordTrace_append hprefix tailTrace_1746012
  have hstable : (prefixWord ++ tailWord_1746012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746012).length < 2 ^ (prefixWord ++ tailWord_1746012).sum := by decide
  have hdescent : baseEnd_1746012 < baseStart_1746012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746032 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3]
def baseStart_1746032 : Nat := 118140960795 + 1746032 * 2 ^ 59
def prefixEnd_1746032 : Nat := 4983230072969 + 3 ^ 40 * 1746032 * 2
def baseEnd_1746032 : Nat := 896553654131217875470151

theorem tailTrace_1746032 : CollatzResearch.WordTrace tailWord_1746032 prefixEnd_1746032 896553654131217875470151 := by
  unfold tailWord_1746032
  simp only [CollatzResearch.WordTrace]
  refine ⟨31841509405215868684956175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42455345873621158246608233 31841509405215868684956175)
  ·
    refine ⟨47762264107823803027434263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31841509405215868684956175 47762264107823803027434263)
    ·
      refine ⟨71643396161735704541151395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47762264107823803027434263 71643396161735704541151395)
      ·
        refine ⟨107465094242603556811727093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71643396161735704541151395 107465094242603556811727093)
        ·
          refine ⟨10074852585244083451099415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107465094242603556811727093 10074852585244083451099415)
          ·
            refine ⟨15112278877866125176649123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10074852585244083451099415 15112278877866125176649123)
            ·
              refine ⟨22668418316799187764973685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15112278877866125176649123 22668418316799187764973685)
              ·
                refine ⟨2125164217199923852966283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22668418316799187764973685 2125164217199923852966283)
                ·
                  refine ⟨3187746325799885779449425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125164217199923852966283 3187746325799885779449425)
                  ·
                    refine ⟨2390809744349914334587069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3187746325799885779449425 2390809744349914334587069)
                    ·
                      refine ⟨896553654131217875470151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390809744349914334587069 896553654131217875470151)
                      ·
                        rfl

theorem cell23_1746032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_1746032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746032 prefixEnd_1746032 := by exact prefixLift 1746032
  have htrace : WordTrace (prefixWord ++ tailWord_1746032) baseStart_1746032 baseEnd_1746032 := by
    simpa [prefixWord, tailWord_1746032, baseEnd_1746032] using wordTrace_append hprefix tailTrace_1746032
  have hstable : (prefixWord ++ tailWord_1746032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746032).length < 2 ^ (prefixWord ++ tailWord_1746032).sum := by decide
  have hdescent : baseEnd_1746032 < baseStart_1746032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746066 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1746066 : Nat := 118140960795 + 1746066 * 2 ^ 59
def prefixEnd_1746066 : Nat := 4983230072969 + 3 ^ 40 * 1746066 * 2
def baseEnd_1746066 : Nat := 896571112473470742444995

theorem tailTrace_1746066 : CollatzResearch.WordTrace tailWord_1746066 prefixEnd_1746066 896571112473470742444995 := by
  unfold tailWord_1746066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921064723077140294162513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42456172594872374117766701 15921064723077140294162513)
  ·
    refine ⟨11940798542307855220621885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15921064723077140294162513 11940798542307855220621885)
    ·
      refine ⟨4477799453365445707733207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11940798542307855220621885 4477799453365445707733207)
      ·
        refine ⟨6716699180048168561599811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477799453365445707733207 6716699180048168561599811)
        ·
          refine ⟨10075048770072252842399717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716699180048168561599811 10075048770072252842399717)
          ·
            refine ⟨1889071644388547407949947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10075048770072252842399717 1889071644388547407949947)
            ·
              refine ⟨2833607466582821111924921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889071644388547407949947 2833607466582821111924921)
              ·
                refine ⟨2125205599937115833943691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833607466582821111924921 2125205599937115833943691)
                ·
                  refine ⟨3187808399905673750915537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125205599937115833943691 3187808399905673750915537)
                  ·
                    refine ⟨2390856299929255313186653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3187808399905673750915537 2390856299929255313186653)
                    ·
                      refine ⟨896571112473470742444995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390856299929255313186653 896571112473470742444995)
                      ·
                        rfl

theorem cell23_1746066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1746066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746066 prefixEnd_1746066 := by exact prefixLift 1746066
  have htrace : WordTrace (prefixWord ++ tailWord_1746066) baseStart_1746066 baseEnd_1746066 := by
    simpa [prefixWord, tailWord_1746066, baseEnd_1746066] using wordTrace_append hprefix tailTrace_1746066
  have hstable : (prefixWord ++ tailWord_1746066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746066).length < 2 ^ (prefixWord ++ tailWord_1746066).sum := by decide
  have hdescent : baseEnd_1746066 < baseStart_1746066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746079 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1746079 : Nat := 118140960795 + 1746079 * 2 ^ 59
def prefixEnd_1746079 : Nat := 4983230072969 + 3 ^ 40 * 1746079 * 2
def baseEnd_1746079 : Nat := 896577787721979191582435

theorem tailTrace_1746079 : CollatzResearch.WordTrace tailWord_1746079 prefixEnd_1746079 896577787721979191582435 := by
  unfold tailWord_1746079
  simp only [CollatzResearch.WordTrace]
  refine ⟨63684733041261464396873291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42456488694174309597915527 63684733041261464396873291)
  ·
    refine ⟨95527099561892196595309937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63684733041261464396873291 95527099561892196595309937)
    ·
      refine ⟨71645324671419147446482453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95527099561892196595309937 71645324671419147446482453)
      ·
        refine ⟨3358374593972772536553865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71645324671419147446482453 3358374593972772536553865)
        ·
          refine ⟨2518780945479579402415399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3358374593972772536553865 2518780945479579402415399)
          ·
            refine ⟨3778171418219369103623099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518780945479579402415399 3778171418219369103623099)
            ·
              refine ⟨5667257127329053655434649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778171418219369103623099 5667257127329053655434649)
              ·
                refine ⟨4250442845496790241575987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667257127329053655434649 4250442845496790241575987)
                ·
                  refine ⟨6375664268245185362363981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250442845496790241575987 6375664268245185362363981)
                  ·
                    refine ⟨2390874100591944510886493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6375664268245185362363981 2390874100591944510886493)
                    ·
                      refine ⟨896577787721979191582435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390874100591944510886493 896577787721979191582435)
                      ·
                        rfl

theorem cell23_1746079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1746079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746079 prefixEnd_1746079 := by exact prefixLift 1746079
  have htrace : WordTrace (prefixWord ++ tailWord_1746079) baseStart_1746079 baseEnd_1746079 := by
    simpa [prefixWord, tailWord_1746079, baseEnd_1746079] using wordTrace_append hprefix tailTrace_1746079
  have hstable : (prefixWord ++ tailWord_1746079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746079).length < 2 ^ (prefixWord ++ tailWord_1746079).sum := by decide
  have hdescent : baseEnd_1746079 < baseStart_1746079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746112 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 2, 6]
def baseStart_1746112 : Nat := 118140960795 + 1746112 * 2 ^ 59
def prefixEnd_1746112 : Nat := 4983230072969 + 3 ^ 40 * 1746112 * 2
def baseEnd_1746112 : Nat := 298864910861192520823261

theorem tailTrace_1746112 : CollatzResearch.WordTrace tailWord_1746112 prefixEnd_1746112 298864910861192520823261 := by
  unfold tailWord_1746112
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842968325070955516412295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42457291100094607355216393 31842968325070955516412295)
  ·
    refine ⟨47764452487606433274618443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31842968325070955516412295 47764452487606433274618443)
    ·
      refine ⟨71646678731409649911927665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47764452487606433274618443 71646678731409649911927665)
      ·
        refine ⟨53735009048557237433945749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71646678731409649911927665 53735009048557237433945749)
        ·
          refine ⟨2518828549151120504716207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53735009048557237433945749 2518828549151120504716207)
          ·
            refine ⟨3778242823726680757074311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518828549151120504716207 3778242823726680757074311)
            ·
              refine ⟨5667364235590021135611467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778242823726680757074311 5667364235590021135611467)
              ·
                refine ⟨8501046353385031703417201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667364235590021135611467 8501046353385031703417201)
                ·
                  refine ⟨6375784765038773777562901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8501046353385031703417201 6375784765038773777562901)
                  ·
                    refine ⟨298864910861192520823261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6375784765038773777562901 298864910861192520823261)
                    ·
                      rfl

theorem cell23_1746112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_1746112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746112 prefixEnd_1746112 := by exact prefixLift 1746112
  have htrace : WordTrace (prefixWord ++ tailWord_1746112) baseStart_1746112 baseEnd_1746112 := by
    simpa [prefixWord, tailWord_1746112, baseEnd_1746112] using wordTrace_append hprefix tailTrace_1746112
  have hstable : (prefixWord ++ tailWord_1746112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746112).length < 2 ^ (prefixWord ++ tailWord_1746112).sum := by decide
  have hdescent : baseEnd_1746112 < baseStart_1746112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746152 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1746152 : Nat := 118140960795 + 1746152 * 2 ^ 59
def prefixEnd_1746152 : Nat := 4983230072969 + 3 ^ 40 * 1746152 * 2
def baseEnd_1746152 : Nat := 896615271809757405969599

theorem tailTrace_1746152 : CollatzResearch.WordTrace tailWord_1746152 prefixEnd_1746152 896615271809757405969599 := by
  unfold tailWord_1746152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31843697784998498932140355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42458263713331331909520473 31843697784998498932140355)
  ·
    refine ⟨47765546677497748398210533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31843697784998498932140355 47765546677497748398210533)
    ·
      refine ⟨8956040002030827824664475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47765546677497748398210533 8956040002030827824664475)
      ·
        refine ⟨13434060003046241736996713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956040002030827824664475 13434060003046241736996713)
        ·
          refine ⟨10075545002284681302747535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13434060003046241736996713 10075545002284681302747535)
          ·
            refine ⟨15113317503427021954121303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075545002284681302747535 15113317503427021954121303)
            ·
              refine ⟨22669976255140532931181955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15113317503427021954121303 22669976255140532931181955)
              ·
                refine ⟨34004964382710799396772933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22669976255140532931181955 34004964382710799396772933)
                ·
                  refine ⟨6375930821758274886894925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34004964382710799396772933 6375930821758274886894925)
                  ·
                    refine ⟨2390974058159353082585597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6375930821758274886894925 2390974058159353082585597)
                    ·
                      refine ⟨896615271809757405969599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2390974058159353082585597 896615271809757405969599)
                      ·
                        rfl

theorem cell23_1746152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1746152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746152 prefixEnd_1746152 := by exact prefixLift 1746152
  have htrace : WordTrace (prefixWord ++ tailWord_1746152) baseStart_1746152 baseEnd_1746152 := by
    simpa [prefixWord, tailWord_1746152, baseEnd_1746152] using wordTrace_append hprefix tailTrace_1746152
  have hstable : (prefixWord ++ tailWord_1746152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746152).length < 2 ^ (prefixWord ++ tailWord_1746152).sum := by decide
  have hdescent : baseEnd_1746152 < baseStart_1746152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746185 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 2, 8]
def baseStart_1746185 : Nat := 118140960795 + 1746185 * 2 ^ 59
def prefixEnd_1746185 : Nat := 4983230072969 + 3 ^ 40 * 1746185 * 2
def baseEnd_1746185 : Nat := 298877405557118592285649

theorem tailTrace_1746185 : CollatzResearch.WordTrace tailWord_1746185 prefixEnd_1746185 298877405557118592285649 := by
  unfold tailWord_1746185
  simp only [CollatzResearch.WordTrace]
  refine ⟨63688599178877444500232009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42459066119251629666821339 63688599178877444500232009)
  ·
    refine ⟨47766449384158083375174007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63688599178877444500232009 47766449384158083375174007)
    ·
      refine ⟨71649674076237125062761011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47766449384158083375174007 71649674076237125062761011)
      ·
        refine ⟨107474511114355687594141517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71649674076237125062761011 107474511114355687594141517)
        ·
          refine ⟨40302941667883382847803069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107474511114355687594141517 40302941667883382847803069)
          ·
            refine ⟨15113603125456268567926151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40302941667883382847803069 15113603125456268567926151)
            ·
              refine ⟨22670404688184402851889227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15113603125456268567926151 22670404688184402851889227)
              ·
                refine ⟨34005607032276604277833841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22670404688184402851889227 34005607032276604277833841)
                ·
                  refine ⟨25504205274207453208375381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34005607032276604277833841 25504205274207453208375381)
                  ·
                    refine ⟨298877405557118592285649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25504205274207453208375381 298877405557118592285649)
                    ·
                      rfl

theorem cell23_1746185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_1746185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746185 prefixEnd_1746185 := by exact prefixLift 1746185
  have htrace : WordTrace (prefixWord ++ tailWord_1746185) baseStart_1746185 baseEnd_1746185 := by
    simpa [prefixWord, tailWord_1746185, baseEnd_1746185] using wordTrace_append hprefix tailTrace_1746185
  have hstable : (prefixWord ++ tailWord_1746185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746185).length < 2 ^ (prefixWord ++ tailWord_1746185).sum := by decide
  have hdescent : baseEnd_1746185 < baseStart_1746185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746195 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5]
def baseStart_1746195 : Nat := 118140960795 + 1746195 * 2 ^ 59
def prefixEnd_1746195 : Nat := 4983230072969 + 3 ^ 40 * 1746195 * 2
def baseEnd_1746195 : Nat := 896637351477900737731901

theorem tailTrace_1746195 : CollatzResearch.WordTrace tailWord_1746195 prefixEnd_1746195 896637351477900737731901 := by
  unfold tailWord_1746195
  simp only [CollatzResearch.WordTrace]
  refine ⟨63688963908841216208096039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42459309272560810805397359 63688963908841216208096039)
  ·
    refine ⟨95533445863261824312144059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63688963908841216208096039 95533445863261824312144059)
    ·
      refine ⟨143300168794892736468216089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95533445863261824312144059 143300168794892736468216089)
      ·
        refine ⟨107475126596169552351162067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143300168794892736468216089 107475126596169552351162067)
        ·
          refine ⟨161212689894254328526743101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107475126596169552351162067 161212689894254328526743101)
          ·
            refine ⟨60454758710345373197528663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161212689894254328526743101 60454758710345373197528663)
            ·
              refine ⟨90682138065518059796292995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60454758710345373197528663 90682138065518059796292995)
              ·
                refine ⟨136023207098277089694439493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90682138065518059796292995 136023207098277089694439493)
                ·
                  refine ⟨25504351330926954317707405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136023207098277089694439493 25504351330926954317707405)
                  ·
                    refine ⟨9564131749097607869140277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25504351330926954317707405 9564131749097607869140277)
                    ·
                      refine ⟨896637351477900737731901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9564131749097607869140277 896637351477900737731901)
                      ·
                        rfl

theorem cell23_1746195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_1746195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746195 prefixEnd_1746195 := by exact prefixLift 1746195
  have htrace : WordTrace (prefixWord ++ tailWord_1746195) baseStart_1746195 baseEnd_1746195 := by
    simpa [prefixWord, tailWord_1746195, baseEnd_1746195] using wordTrace_append hprefix tailTrace_1746195
  have hstable : (prefixWord ++ tailWord_1746195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746195).length < 2 ^ (prefixWord ++ tailWord_1746195).sum := by decide
  have hdescent : baseEnd_1746195 < baseStart_1746195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746235 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8]
def baseStart_1746235 : Nat := 118140960795 + 1746235 * 2 ^ 59
def prefixEnd_1746235 : Nat := 4983230072969 + 3 ^ 40 * 1746235 * 2
def baseEnd_1746235 : Nat := 896657890704080581231717

theorem tailTrace_1746235 : CollatzResearch.WordTrace tailWord_1746235 prefixEnd_1746235 896657890704080581231717 := by
  unfold tailWord_1746235
  simp only [CollatzResearch.WordTrace]
  refine ⟨63690422828696303039552159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42460281885797535359701439 63690422828696303039552159)
  ·
    refine ⟨95535634243044454559328239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63690422828696303039552159 95535634243044454559328239)
    ·
      refine ⟨143303451364566681838992359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95535634243044454559328239 143303451364566681838992359)
      ·
        refine ⟨214955177046850022758488539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143303451364566681838992359 214955177046850022758488539)
        ·
          refine ⟨322432765570275034137732809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214955177046850022758488539 322432765570275034137732809)
          ·
            refine ⟨241824574177706275603299607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322432765570275034137732809 241824574177706275603299607)
            ·
              refine ⟨362736861266559413404949411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241824574177706275603299607 362736861266559413404949411)
              ·
                refine ⟨544105291899839120107424117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362736861266559413404949411 544105291899839120107424117)
                ·
                  refine ⟨51009871115609917510071011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544105291899839120107424117 51009871115609917510071011)
                  ·
                    refine ⟨76514806673414876265106517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51009871115609917510071011 76514806673414876265106517)
                    ·
                      refine ⟨896657890704080581231717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 76514806673414876265106517 896657890704080581231717)
                      ·
                        rfl

theorem cell23_1746235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_1746235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746235 prefixEnd_1746235 := by exact prefixLift 1746235
  have htrace : WordTrace (prefixWord ++ tailWord_1746235) baseStart_1746235 baseEnd_1746235 := by
    simpa [prefixWord, tailWord_1746235, baseEnd_1746235] using wordTrace_append hprefix tailTrace_1746235
  have hstable : (prefixWord ++ tailWord_1746235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746235).length < 2 ^ (prefixWord ++ tailWord_1746235).sum := by decide
  have hdescent : baseEnd_1746235 < baseStart_1746235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746293 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1746293 : Nat := 118140960795 + 1746293 * 2 ^ 59
def prefixEnd_1746293 : Nat := 4983230072969 + 3 ^ 40 * 1746293 * 2
def baseEnd_1746293 : Nat := 896687672582041354306451

theorem tailTrace_1746293 : CollatzResearch.WordTrace tailWord_1746293 prefixEnd_1746293 896687672582041354306451 := by
  unfold tailWord_1746293
  simp only [CollatzResearch.WordTrace]
  refine ⟨63692538262486178945163533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42461692174990785963442355 63692538262486178945163533)
  ·
    refine ⟨23884701848432317104436325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63692538262486178945163533 23884701848432317104436325)
    ·
      refine ⟨4478381596581059457081811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23884701848432317104436325 4478381596581059457081811)
      ·
        refine ⟨6717572394871589185622717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478381596581059457081811 6717572394871589185622717)
        ·
          refine ⟨2519089648076845944608519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6717572394871589185622717 2519089648076845944608519)
          ·
            refine ⟨3778634472115268916912779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519089648076845944608519 3778634472115268916912779)
            ·
              refine ⟨5667951708172903375369169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778634472115268916912779 5667951708172903375369169)
              ·
                refine ⟨4250963781129677531526877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667951708172903375369169 4250963781129677531526877)
                ·
                  refine ⟨1594111417923629074322579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4250963781129677531526877 1594111417923629074322579)
                  ·
                    refine ⟨2391167126885443611483869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1594111417923629074322579 2391167126885443611483869)
                    ·
                      refine ⟨896687672582041354306451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2391167126885443611483869 896687672582041354306451)
                      ·
                        rfl

theorem cell23_1746293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1746293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746293 prefixEnd_1746293 := by exact prefixLift 1746293
  have htrace : WordTrace (prefixWord ++ tailWord_1746293) baseStart_1746293 baseEnd_1746293 := by
    simpa [prefixWord, tailWord_1746293, baseEnd_1746293] using wordTrace_append hprefix tailTrace_1746293
  have hstable : (prefixWord ++ tailWord_1746293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746293).length < 2 ^ (prefixWord ++ tailWord_1746293).sum := by decide
  have hdescent : baseEnd_1746293 < baseStart_1746293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746299 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 4]
def baseStart_1746299 : Nat := 118140960795 + 1746299 * 2 ^ 59
def prefixEnd_1746299 : Nat := 4983230072969 + 3 ^ 40 * 1746299 * 2
def baseEnd_1746299 : Nat := 896690753465968330831423

theorem tailTrace_1746299 : CollatzResearch.WordTrace tailWord_1746299 prefixEnd_1746299 896690753465968330831423 := by
  unfold tailWord_1746299
  simp only [CollatzResearch.WordTrace]
  refine ⟨63692757100464441969881951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42461838066976294646587967 63692757100464441969881951)
  ·
    refine ⟨95539135650696662954822927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63692757100464441969881951 95539135650696662954822927)
    ·
      refine ⟨143308703476044994432234391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95539135650696662954822927 143308703476044994432234391)
      ·
        refine ⟨214963055214067491648351587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143308703476044994432234391 214963055214067491648351587)
        ·
          refine ⟨322444582821101237472527381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214963055214067491648351587 322444582821101237472527381)
          ·
            refine ⟨15114589819739120506524721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 322444582821101237472527381 15114589819739120506524721)
            ·
              refine ⟨11335942364804340379893541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15114589819739120506524721 11335942364804340379893541)
              ·
                refine ⟨2125489193400813821230039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11335942364804340379893541 2125489193400813821230039)
                ·
                  refine ⟨3188233790101220731845059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125489193400813821230039 3188233790101220731845059)
                  ·
                    refine ⟨4782350685151831097767589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3188233790101220731845059 4782350685151831097767589)
                    ·
                      refine ⟨896690753465968330831423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4782350685151831097767589 896690753465968330831423)
                      ·
                        rfl

theorem cell23_1746299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 4].length) (baseStart_1746299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746299 prefixEnd_1746299 := by exact prefixLift 1746299
  have htrace : WordTrace (prefixWord ++ tailWord_1746299) baseStart_1746299 baseEnd_1746299 := by
    simpa [prefixWord, tailWord_1746299, baseEnd_1746299] using wordTrace_append hprefix tailTrace_1746299
  have hstable : (prefixWord ++ tailWord_1746299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746299).length < 2 ^ (prefixWord ++ tailWord_1746299).sum := by decide
  have hdescent : baseEnd_1746299 < baseStart_1746299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746313 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 1, 5]
def baseStart_1746313 : Nat := 118140960795 + 1746313 * 2 ^ 59
def prefixEnd_1746313 : Nat := 4983230072969 + 3 ^ 40 * 1746313 * 2
def baseEnd_1746313 : Nat := 298899314065043758685453

theorem tailTrace_1746313 : CollatzResearch.WordTrace tailWord_1746313 prefixEnd_1746313 298899314065043758685453 := by
  unfold tailWord_1746313
  simp only [CollatzResearch.WordTrace]
  refine ⟨63693267722413722360891593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42462178481609148240594395 63693267722413722360891593)
  ·
    refine ⟨47769950791810291770668695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63693267722413722360891593 47769950791810291770668695)
    ·
      refine ⟨71654926187715437656003043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47769950791810291770668695 71654926187715437656003043)
      ·
        refine ⟨107482389281573156484004565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71654926187715437656003043 107482389281573156484004565)
        ·
          refine ⟨2519118498786870855093857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 107482389281573156484004565 2519118498786870855093857)
          ·
            refine ⟨1889338874090153141320393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2519118498786870855093857 1889338874090153141320393)
            ·
              refine ⟨1417004155567614855990295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889338874090153141320393 1417004155567614855990295)
              ·
                refine ⟨2125506233351422283985443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417004155567614855990295 2125506233351422283985443)
                ·
                  refine ⟨3188259350027133425978165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125506233351422283985443 3188259350027133425978165)
                  ·
                    refine ⟨298899314065043758685453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3188259350027133425978165 298899314065043758685453)
                    ·
                      rfl

theorem cell23_1746313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 5].length) (baseStart_1746313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746313 prefixEnd_1746313 := by exact prefixLift 1746313
  have htrace : WordTrace (prefixWord ++ tailWord_1746313) baseStart_1746313 baseEnd_1746313 := by
    simpa [prefixWord, tailWord_1746313, baseEnd_1746313] using wordTrace_append hprefix tailTrace_1746313
  have hstable : (prefixWord ++ tailWord_1746313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746313).length < 2 ^ (prefixWord ++ tailWord_1746313).sum := by decide
  have hdescent : baseEnd_1746313 < baseStart_1746313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746316 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 5, 2, 2]
def baseStart_1746316 : Nat := 118140960795 + 1746316 * 2 ^ 59
def prefixEnd_1746316 : Nat := 4983230072969 + 3 ^ 40 * 1746316 * 2
def baseEnd_1746316 : Nat := 896699482637094764318845

theorem tailTrace_1746316 : CollatzResearch.WordTrace tailWord_1746316 prefixEnd_1746316 896699482637094764318845 := by
  unfold tailWord_1746316
  simp only [CollatzResearch.WordTrace]
  refine ⟨31846688570701426936625401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42462251427601902582167201 31846688570701426936625401)
  ·
    refine ⟨23885016428026070202469051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31846688570701426936625401 23885016428026070202469051)
    ·
      refine ⟨35827524642039105303703577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23885016428026070202469051 35827524642039105303703577)
      ·
        refine ⟨26870643481529328977777683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35827524642039105303703577 26870643481529328977777683)
        ·
          refine ⟨40305965222293993466666525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26870643481529328977777683 40305965222293993466666525)
          ·
            refine ⟨15114736958360247549999947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40305965222293993466666525 15114736958360247549999947)
            ·
              refine ⟨22672105437540371324999921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15114736958360247549999947 22672105437540371324999921)
              ·
                refine ⟨17004079078155278493749941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22672105437540371324999921 17004079078155278493749941)
                ·
                  refine ⟨1594132413577057358789057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17004079078155278493749941 1594132413577057358789057)
                  ·
                    refine ⟨1195599310182793019091793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1594132413577057358789057 1195599310182793019091793)
                    ·
                      refine ⟨896699482637094764318845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195599310182793019091793 896699482637094764318845)
                      ·
                        rfl

theorem cell23_1746316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_1746316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746316 prefixEnd_1746316 := by exact prefixLift 1746316
  have htrace : WordTrace (prefixWord ++ tailWord_1746316) baseStart_1746316 baseEnd_1746316 := by
    simpa [prefixWord, tailWord_1746316, baseEnd_1746316] using wordTrace_append hprefix tailTrace_1746316
  have hstable : (prefixWord ++ tailWord_1746316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746316).length < 2 ^ (prefixWord ++ tailWord_1746316).sum := by decide
  have hdescent : baseEnd_1746316 < baseStart_1746316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746333 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_1746333 : Nat := 118140960795 + 1746333 * 2 ^ 59
def prefixEnd_1746333 : Nat := 4983230072969 + 3 ^ 40 * 1746333 * 2
def baseEnd_1746333 : Nat := 896708211808221197806267

theorem tailTrace_1746333 : CollatzResearch.WordTrace tailWord_1746333 prefixEnd_1746333 896708211808221197806267 := by
  unfold tailWord_1746333
  simp only [CollatzResearch.WordTrace]
  refine ⟨63693997182341265776619653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42462664788227510517746435 63693997182341265776619653)
  ·
    refine ⟨11942624471688987333116185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63693997182341265776619653 11942624471688987333116185)
    ·
      refine ⟨8956968353766740499837139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11942624471688987333116185 8956968353766740499837139)
      ·
        refine ⟨13435452530650110749755709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956968353766740499837139 13435452530650110749755709)
        ·
          refine ⟨5038294698993791531158391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13435452530650110749755709 5038294698993791531158391)
          ·
            refine ⟨7557442048490687296737587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038294698993791531158391 7557442048490687296737587)
            ·
              refine ⟨11336163072736030945106381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557442048490687296737587 11336163072736030945106381)
              ·
                refine ⟨4251061152276011604414893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11336163072736030945106381 4251061152276011604414893)
                ·
                  refine ⟨1594147932103504351655585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4251061152276011604414893 1594147932103504351655585)
                  ·
                    refine ⟨1195610949077628263741689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1594147932103504351655585 1195610949077628263741689)
                    ·
                      refine ⟨896708211808221197806267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195610949077628263741689 896708211808221197806267)
                      ·
                        rfl

theorem cell23_1746333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_1746333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746333 prefixEnd_1746333 := by exact prefixLift 1746333
  have htrace : WordTrace (prefixWord ++ tailWord_1746333) baseStart_1746333 baseEnd_1746333 := by
    simpa [prefixWord, tailWord_1746333, baseEnd_1746333] using wordTrace_append hprefix tailTrace_1746333
  have hstable : (prefixWord ++ tailWord_1746333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746333).length < 2 ^ (prefixWord ++ tailWord_1746333).sum := by decide
  have hdescent : baseEnd_1746333 < baseStart_1746333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746343 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1746343 : Nat := 118140960795 + 1746343 * 2 ^ 59
def prefixEnd_1746343 : Nat := 4983230072969 + 3 ^ 40 * 1746343 * 2
def baseEnd_1746343 : Nat := 298904448871588719560407

theorem tailTrace_1746343 : CollatzResearch.WordTrace tailWord_1746343 prefixEnd_1746343 298904448871588719560407 := by
  unfold tailWord_1746343
  simp only [CollatzResearch.WordTrace]
  refine ⟨63694361912305037484483683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42462907941536691656322455 63694361912305037484483683)
  ·
    refine ⟨95541542868457556226725525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63694361912305037484483683 95541542868457556226725525)
    ·
      refine ⟨4478509821958947948127759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95541542868457556226725525 4478509821958947948127759)
      ·
        refine ⟨6717764732938421922191639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478509821958947948127759 6717764732938421922191639)
        ·
          refine ⟨10076647099407632883287459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717764732938421922191639 10076647099407632883287459)
          ·
            refine ⟨15114970649111449324931189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076647099407632883287459 15114970649111449324931189)
            ·
              refine ⟨1417028498354198374212299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15114970649111449324931189 1417028498354198374212299)
              ·
                refine ⟨2125542747531297561318449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417028498354198374212299 2125542747531297561318449)
                ·
                  refine ⟨1594157060648473170988837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2125542747531297561318449 1594157060648473170988837)
                  ·
                    refine ⟨298904448871588719560407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1594157060648473170988837 298904448871588719560407)
                    ·
                      rfl

theorem cell23_1746343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1746343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746343 prefixEnd_1746343 := by exact prefixLift 1746343
  have htrace : WordTrace (prefixWord ++ tailWord_1746343) baseStart_1746343 baseEnd_1746343 := by
    simpa [prefixWord, tailWord_1746343, baseEnd_1746343] using wordTrace_append hprefix tailTrace_1746343
  have hstable : (prefixWord ++ tailWord_1746343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746343).length < 2 ^ (prefixWord ++ tailWord_1746343).sum := by decide
  have hdescent : baseEnd_1746343 < baseStart_1746343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746389 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1746389 : Nat := 118140960795 + 1746389 * 2 ^ 59
def prefixEnd_1746389 : Nat := 4983230072969 + 3 ^ 40 * 1746389 * 2
def baseEnd_1746389 : Nat := 896736966724872978706009

theorem tailTrace_1746389 : CollatzResearch.WordTrace tailWord_1746389 prefixEnd_1746389 896736966724872978706009 := by
  unfold tailWord_1746389
  simp only [CollatzResearch.WordTrace]
  refine ⟨63696039670138387340658221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42464026446758924893772147 63696039670138387340658221)
  ·
    refine ⟨23886014876301895252746833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63696039670138387340658221 23886014876301895252746833)
    ·
      refine ⟨17914511157226421439560125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23886014876301895252746833 17914511157226421439560125)
      ·
        refine ⟨6717941683959908039835047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17914511157226421439560125 6717941683959908039835047)
        ·
          refine ⟨10076912525939862059752571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717941683959908039835047 10076912525939862059752571)
          ·
            refine ⟨15115368788909793089628857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076912525939862059752571 15115368788909793089628857)
            ·
              refine ⟨11336526591682344817221643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15115368788909793089628857 11336526591682344817221643)
              ·
                refine ⟨17004789887523517225832465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11336526591682344817221643 17004789887523517225832465)
                ·
                  refine ⟨12753592415642637919374349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17004789887523517225832465 12753592415642637919374349)
                  ·
                    refine ⟨4782597155865989219765381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12753592415642637919374349 4782597155865989219765381)
                    ·
                      refine ⟨896736966724872978706009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4782597155865989219765381 896736966724872978706009)
                      ·
                        rfl

theorem cell23_1746389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1746389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746389 prefixEnd_1746389 := by exact prefixLift 1746389
  have htrace : WordTrace (prefixWord ++ tailWord_1746389) baseStart_1746389 baseEnd_1746389 := by
    simpa [prefixWord, tailWord_1746389, baseEnd_1746389] using wordTrace_append hprefix tailTrace_1746389
  have hstable : (prefixWord ++ tailWord_1746389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746389).length < 2 ^ (prefixWord ++ tailWord_1746389).sum := by decide
  have hdescent : baseEnd_1746389 < baseStart_1746389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746516 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_1746516 : Nat := 118140960795 + 1746516 * 2 ^ 59
def prefixEnd_1746516 : Nat := 4983230072969 + 3 ^ 40 * 1746516 * 2
def baseEnd_1746516 : Nat := 896802178767993981817925

theorem tailTrace_1746516 : CollatzResearch.WordTrace tailWord_1746516 prefixEnd_1746516 896802178767993981817925 := by
  unfold tailWord_1746516
  simp only [CollatzResearch.WordTrace]
  refine ⟨31850335870339144015265701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42467114493785525353687601 31850335870339144015265701)
  ·
    refine ⟨5971937975688589502862319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31850335870339144015265701 5971937975688589502862319)
    ·
      refine ⟨8957906963532884254293479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971937975688589502862319 8957906963532884254293479)
      ·
        refine ⟨13436860445299326381440219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8957906963532884254293479 13436860445299326381440219)
        ·
          refine ⟨20155290667948989572160329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13436860445299326381440219 20155290667948989572160329)
          ·
            refine ⟨15116468000961742179120247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20155290667948989572160329 15116468000961742179120247)
            ·
              refine ⟨22674702001442613268680371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15116468000961742179120247 22674702001442613268680371)
              ·
                refine ⟨34012053002163919903020557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22674702001442613268680371 34012053002163919903020557)
                ·
                  refine ⟨12754519875811469963632709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34012053002163919903020557 12754519875811469963632709)
                  ·
                    refine ⟨2391472476714650618181133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12754519875811469963632709 2391472476714650618181133)
                    ·
                      refine ⟨896802178767993981817925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2391472476714650618181133 896802178767993981817925)
                      ·
                        rfl

theorem cell23_1746516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_1746516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746516 prefixEnd_1746516 := by exact prefixLift 1746516
  have htrace : WordTrace (prefixWord ++ tailWord_1746516) baseStart_1746516 baseEnd_1746516 := by
    simpa [prefixWord, tailWord_1746516, baseEnd_1746516] using wordTrace_append hprefix tailTrace_1746516
  have hstable : (prefixWord ++ tailWord_1746516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746516).length < 2 ^ (prefixWord ++ tailWord_1746516).sum := by decide
  have hdescent : baseEnd_1746516 < baseStart_1746516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746536 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 8]
def baseStart_1746536 : Nat := 118140960795 + 1746536 * 2 ^ 59
def prefixEnd_1746536 : Nat := 4983230072969 + 3 ^ 40 * 1746536 * 2
def baseEnd_1746536 : Nat := 99645827597898211507537

theorem tailTrace_1746536 : CollatzResearch.WordTrace tailWord_1746536 prefixEnd_1746536 99645827597898211507537 := by
  unfold tailWord_1746536
  simp only [CollatzResearch.WordTrace]
  refine ⟨31850700600302915723129731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42467600800403887630839641 31850700600302915723129731)
  ·
    refine ⟨47776050900454373584694597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31850700600302915723129731 47776050900454373584694597)
    ·
      refine ⟨8958009543835195047130237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47776050900454373584694597 8958009543835195047130237)
      ·
        refine ⟨3359253578938198142673839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8958009543835195047130237 3359253578938198142673839)
        ·
          refine ⟨5038880368407297214010759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359253578938198142673839 5038880368407297214010759)
          ·
            refine ⟨7558320552610945821016139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038880368407297214010759 7558320552610945821016139)
            ·
              refine ⟨11337480828916418731524209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558320552610945821016139 11337480828916418731524209)
              ·
                refine ⟨8503110621687314048643157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11337480828916418731524209 8503110621687314048643157)
                ·
                  refine ⟨99645827597898211507537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8503110621687314048643157 99645827597898211507537)
                  ·
                    rfl

theorem cell23_1746536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 8].length) (baseStart_1746536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746536 prefixEnd_1746536 := by exact prefixLift 1746536
  have htrace : WordTrace (prefixWord ++ tailWord_1746536) baseStart_1746536 baseEnd_1746536 := by
    simpa [prefixWord, tailWord_1746536, baseEnd_1746536] using wordTrace_append hprefix tailTrace_1746536
  have hstable : (prefixWord ++ tailWord_1746536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746536).length < 2 ^ (prefixWord ++ tailWord_1746536).sum := by decide
  have hdescent : baseEnd_1746536 < baseStart_1746536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746550 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1746550 : Nat := 118140960795 + 1746550 * 2 ^ 59
def prefixEnd_1746550 : Nat := 4983230072969 + 3 ^ 40 * 1746550 * 2
def baseEnd_1746550 : Nat := 896819637110246848792769

theorem tailTrace_1746550 : CollatzResearch.WordTrace tailWord_1746550 prefixEnd_1746550 896819637110246848792769 := by
  unfold tailWord_1746550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981369488909694489829319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42467941215036741224846069 3981369488909694489829319)
  ·
    refine ⟨5972054233364541734743979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3981369488909694489829319 5972054233364541734743979)
    ·
      refine ⟨8958081350046812602115969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5972054233364541734743979 8958081350046812602115969)
      ·
        refine ⟨6718561012535109451586977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8958081350046812602115969 6718561012535109451586977)
        ·
          refine ⟨5038920759401332088690233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6718561012535109451586977 5038920759401332088690233)
          ·
            refine ⟨3779190569550999066517675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5038920759401332088690233 3779190569550999066517675)
            ·
              refine ⟨5668785854326498599776513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779190569550999066517675 5668785854326498599776513)
              ·
                refine ⟨4251589390744873949832385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5668785854326498599776513 4251589390744873949832385)
                ·
                  refine ⟨3188692043058655462374289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4251589390744873949832385 3188692043058655462374289)
                  ·
                    refine ⟨2391519032293991596780717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3188692043058655462374289 2391519032293991596780717)
                    ·
                      refine ⟨896819637110246848792769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2391519032293991596780717 896819637110246848792769)
                      ·
                        rfl

theorem cell23_1746550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1746550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746550 prefixEnd_1746550 := by exact prefixLift 1746550
  have htrace : WordTrace (prefixWord ++ tailWord_1746550) baseStart_1746550 baseEnd_1746550 := by
    simpa [prefixWord, tailWord_1746550, baseEnd_1746550] using wordTrace_append hprefix tailTrace_1746550
  have hstable : (prefixWord ++ tailWord_1746550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746550).length < 2 ^ (prefixWord ++ tailWord_1746550).sum := by decide
  have hdescent : baseEnd_1746550 < baseStart_1746550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746557 : List Nat := [1, 4, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_1746557 : Nat := 118140960795 + 1746557 * 2 ^ 59
def prefixEnd_1746557 : Nat := 4983230072969 + 3 ^ 40 * 1746557 * 2
def baseEnd_1746557 : Nat := 298941077158276107135079

theorem tailTrace_1746557 : CollatzResearch.WordTrace tailWord_1746557 prefixEnd_1746557 298941077158276107135079 := by
  unfold tailWord_1746557
  simp only [CollatzResearch.WordTrace]
  refine ⟨63702167133529752032773925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42468111422353168021849283 63702167133529752032773925)
  ·
    refine ⟨11944156337536828506145111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63702167133529752032773925 11944156337536828506145111)
    ·
      refine ⟨17916234506305242759217667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11944156337536828506145111 17916234506305242759217667)
      ·
        refine ⟨26874351759457864138826501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17916234506305242759217667 26874351759457864138826501)
        ·
          refine ⟨5038940954898349526029969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26874351759457864138826501 5038940954898349526029969)
          ·
            refine ⟨3779205716173762144522477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5038940954898349526029969 3779205716173762144522477)
            ·
              refine ⟨1417202143565160804195929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3779205716173762144522477 1417202143565160804195929)
              ·
                refine ⟨1062901607673870603146947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417202143565160804195929 1062901607673870603146947)
                ·
                  refine ⟨1594352411510805904720421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062901607673870603146947 1594352411510805904720421)
                  ·
                    refine ⟨298941077158276107135079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1594352411510805904720421 298941077158276107135079)
                    ·
                      rfl

theorem cell23_1746557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_1746557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746557 prefixEnd_1746557 := by exact prefixLift 1746557
  have htrace : WordTrace (prefixWord ++ tailWord_1746557) baseStart_1746557 baseEnd_1746557 := by
    simpa [prefixWord, tailWord_1746557, baseEnd_1746557] using wordTrace_append hprefix tailTrace_1746557
  have hstable : (prefixWord ++ tailWord_1746557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746557).length < 2 ^ (prefixWord ++ tailWord_1746557).sum := by decide
  have hdescent : baseEnd_1746557 < baseStart_1746557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746570 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 6]
def baseStart_1746570 : Nat := 118140960795 + 1746570 * 2 ^ 59
def prefixEnd_1746570 : Nat := 4983230072969 + 3 ^ 40 * 1746570 * 2
def baseEnd_1746570 : Nat := 99647767413704085615853

theorem tailTrace_1746570 : CollatzResearch.WordTrace tailWord_1746570 prefixEnd_1746570 99647767413704085615853 := by
  unfold tailWord_1746570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15925660320620663813249291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42468427521655103501998109 15925660320620663813249291)
  ·
    refine ⟨23888490480930995719873937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15925660320620663813249291 23888490480930995719873937)
    ·
      refine ⟨17916367860698246789905453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23888490480930995719873937 17916367860698246789905453)
      ·
        refine ⟨6718637947761842546214545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17916367860698246789905453 6718637947761842546214545)
        ·
          refine ⟨5038978460821381909660909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6718637947761842546214545 5038978460821381909660909)
          ·
            refine ⟨1889616922808018216122841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5038978460821381909660909 1889616922808018216122841)
            ·
              refine ⟨1417212692106013662092131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889616922808018216122841 1417212692106013662092131)
              ·
                refine ⟨2125819038159020493138197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417212692106013662092131 2125819038159020493138197)
                ·
                  refine ⟨99647767413704085615853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2125819038159020493138197 99647767413704085615853)
                  ·
                    rfl

theorem cell23_1746570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_1746570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746570 prefixEnd_1746570 := by exact prefixLift 1746570
  have htrace : WordTrace (prefixWord ++ tailWord_1746570) baseStart_1746570 baseEnd_1746570 := by
    simpa [prefixWord, tailWord_1746570, baseEnd_1746570] using wordTrace_append hprefix tailTrace_1746570
  have hstable : (prefixWord ++ tailWord_1746570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746570).length < 2 ^ (prefixWord ++ tailWord_1746570).sum := by decide
  have hdescent : baseEnd_1746570 < baseStart_1746570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746583 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 1, 5]
def baseStart_1746583 : Nat := 118140960795 + 1746583 * 2 ^ 59
def prefixEnd_1746583 : Nat := 4983230072969 + 3 ^ 40 * 1746583 * 2
def baseEnd_1746583 : Nat := 298945527323948406560039

theorem tailTrace_1746583 : CollatzResearch.WordTrace tailWord_1746583 prefixEnd_1746583 298945527323948406560039 := by
  unfold tailWord_1746583
  simp only [CollatzResearch.WordTrace]
  refine ⟨63703115431435558473220403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42468743620957038982146935 63703115431435558473220403)
  ·
    refine ⟨95554673147153337709830605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63703115431435558473220403 95554673147153337709830605)
    ·
      refine ⟨35833002430182501641186477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95554673147153337709830605 35833002430182501641186477)
      ·
        refine ⟨13437375911318438115444929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35833002430182501641186477 13437375911318438115444929)
        ·
          refine ⟨10078031933488828586583697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13437375911318438115444929 10078031933488828586583697)
          ·
            refine ⟨7558523950116621439937773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10078031933488828586583697 7558523950116621439937773)
            ·
              refine ⟨2834446481293733039976665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7558523950116621439937773 2834446481293733039976665)
              ·
                refine ⟨2125834860970299779982499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834446481293733039976665 2125834860970299779982499)
                ·
                  refine ⟨3188752291455449669973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125834860970299779982499 3188752291455449669973749)
                  ·
                    refine ⟨298945527323948406560039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3188752291455449669973749 298945527323948406560039)
                    ·
                      rfl

theorem cell23_1746583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_1746583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746583 prefixEnd_1746583 := by exact prefixLift 1746583
  have htrace : WordTrace (prefixWord ++ tailWord_1746583) baseStart_1746583 baseEnd_1746583 := by
    simpa [prefixWord, tailWord_1746583, baseEnd_1746583] using wordTrace_append hprefix tailTrace_1746583
  have hstable : (prefixWord ++ tailWord_1746583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746583).length < 2 ^ (prefixWord ++ tailWord_1746583).sum := by decide
  have hdescent : baseEnd_1746583 < baseStart_1746583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746596 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1746596 : Nat := 118140960795 + 1746596 * 2 ^ 59
def prefixEnd_1746596 : Nat := 4983230072969 + 3 ^ 40 * 1746596 * 2
def baseEnd_1746596 : Nat := 298947752406784556272519

theorem tailTrace_1746596 : CollatzResearch.WordTrace tailWord_1746596 prefixEnd_1746596 298947752406784556272519 := by
  unfold tailWord_1746596
  simp only [CollatzResearch.WordTrace]
  refine ⟨31851794790194230846721821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42469059720258974462295761 31851794790194230846721821)
  ·
    refine ⟨11944423046322836567520683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31851794790194230846721821 11944423046322836567520683)
    ·
      refine ⟨17916634569484254851281025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11944423046322836567520683 17916634569484254851281025)
      ·
        refine ⟨13437475927113191138460769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17916634569484254851281025 13437475927113191138460769)
        ·
          refine ⟨10078106945334893353845577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13437475927113191138460769 10078106945334893353845577)
          ·
            refine ⟨7558580209001170015384183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10078106945334893353845577 7558580209001170015384183)
            ·
              refine ⟨11337870313501755023076275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558580209001170015384183 11337870313501755023076275)
              ·
                refine ⟨17006805470252632534614413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11337870313501755023076275 17006805470252632534614413)
                ·
                  refine ⟨6377552051344737200480405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17006805470252632534614413 6377552051344737200480405)
                  ·
                    refine ⟨298947752406784556272519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6377552051344737200480405 298947752406784556272519)
                    ·
                      rfl

theorem cell23_1746596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1746596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746596 prefixEnd_1746596 := by exact prefixLift 1746596
  have htrace : WordTrace (prefixWord ++ tailWord_1746596) baseStart_1746596 baseEnd_1746596 := by
    simpa [prefixWord, tailWord_1746596, baseEnd_1746596] using wordTrace_append hprefix tailTrace_1746596
  have hstable : (prefixWord ++ tailWord_1746596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746596).length < 2 ^ (prefixWord ++ tailWord_1746596).sum := by decide
  have hdescent : baseEnd_1746596 < baseStart_1746596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746609 : List Nat := [1, 2, 2, 18]
def baseStart_1746609 : Nat := 118140960795 + 1746609 * 2 ^ 59
def prefixEnd_1746609 : Nat := 4983230072969 + 3 ^ 40 * 1746609 * 2
def baseEnd_1746609 : Nat := 410082273648313725631

theorem tailTrace_1746609 : CollatzResearch.WordTrace tailWord_1746609 prefixEnd_1746609 410082273648313725631 := by
  unfold tailWord_1746609
  simp only [CollatzResearch.WordTrace]
  refine ⟨63704063729341364913666881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42469375819560909942444587 63704063729341364913666881)
  ·
    refine ⟨47778047797006023685250161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63704063729341364913666881 47778047797006023685250161)
    ·
      refine ⟨35833535847754517763937621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47778047797006023685250161 35833535847754517763937621)
      ·
        refine ⟨410082273648313725631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 35833535847754517763937621 410082273648313725631)
        ·
          rfl

theorem cell23_1746609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 18].length) (baseStart_1746609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746609 prefixEnd_1746609 := by exact prefixLift 1746609
  have htrace : WordTrace (prefixWord ++ tailWord_1746609) baseStart_1746609 baseEnd_1746609 := by
    simpa [prefixWord, tailWord_1746609, baseEnd_1746609] using wordTrace_append hprefix tailTrace_1746609
  have hstable : (prefixWord ++ tailWord_1746609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746609).length < 2 ^ (prefixWord ++ tailWord_1746609).sum := by decide
  have hdescent : baseEnd_1746609 < baseStart_1746609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746670 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_1746670 : Nat := 118140960795 + 1746670 * 2 ^ 59
def prefixEnd_1746670 : Nat := 4983230072969 + 3 ^ 40 * 1746670 * 2
def baseEnd_1746670 : Nat := 896881254788786379292217

theorem tailTrace_1746670 : CollatzResearch.WordTrace tailWord_1746670 prefixEnd_1746670 896881254788786379292217 := by
  unfold tailWord_1746670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963286072765046541454683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42470859054746914887758309 7963286072765046541454683)
  ·
    refine ⟨11944929109147569812182025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7963286072765046541454683 11944929109147569812182025)
    ·
      refine ⟨8958696831860677359136519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11944929109147569812182025 8958696831860677359136519)
      ·
        refine ⟨13438045247791016038704779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958696831860677359136519 13438045247791016038704779)
        ·
          refine ⟨20157067871686524058057169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13438045247791016038704779 20157067871686524058057169)
          ·
            refine ⟨15117800903764893043542877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20157067871686524058057169 15117800903764893043542877)
            ·
              refine ⟨5669175338911834891328579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15117800903764893043542877 5669175338911834891328579)
              ·
                refine ⟨8503763008367752336992869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669175338911834891328579 8503763008367752336992869)
                ·
                  refine ⟨1594455564068953563186163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8503763008367752336992869 1594455564068953563186163)
                  ·
                    refine ⟨2391683346103430344779245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1594455564068953563186163 2391683346103430344779245)
                    ·
                      refine ⟨896881254788786379292217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2391683346103430344779245 896881254788786379292217)
                      ·
                        rfl

theorem cell23_1746670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_1746670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746670 prefixEnd_1746670 := by exact prefixLift 1746670
  have htrace : WordTrace (prefixWord ++ tailWord_1746670) baseStart_1746670 baseEnd_1746670 := by
    simpa [prefixWord, tailWord_1746670, baseEnd_1746670] using wordTrace_append hprefix tailTrace_1746670
  have hstable : (prefixWord ++ tailWord_1746670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746670).length < 2 ^ (prefixWord ++ tailWord_1746670).sum := by decide
  have hdescent : baseEnd_1746670 < baseStart_1746670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746744 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 2, 2, 2]
def baseStart_1746744 : Nat := 118140960795 + 1746744 * 2 ^ 59
def prefixEnd_1746744 : Nat := 4983230072969 + 3 ^ 40 * 1746744 * 2
def baseEnd_1746744 : Nat := 896919252357219089766877

theorem tailTrace_1746744 : CollatzResearch.WordTrace tailWord_1746744 prefixEnd_1746744 896919252357219089766877 := by
  unfold tailWord_1746744
  simp only [CollatzResearch.WordTrace]
  refine ⟨31854493791926141484915643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42472658389234855313220857 31854493791926141484915643)
  ·
    refine ⟨47781740687889212227373465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31854493791926141484915643 47781740687889212227373465)
    ·
      refine ⟨35836305515916909170530099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47781740687889212227373465 35836305515916909170530099)
      ·
        refine ⟨53754458273875363755795149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35836305515916909170530099 53754458273875363755795149)
        ·
          refine ⟨20157921852703261408423181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53754458273875363755795149 20157921852703261408423181)
          ·
            refine ⟨7559220694763723028158693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20157921852703261408423181 7559220694763723028158693)
            ·
              refine ⟨1417353880268198067779755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7559220694763723028158693 1417353880268198067779755)
              ·
                refine ⟨2126030820402297101669633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417353880268198067779755 2126030820402297101669633)
                ·
                  refine ⟨1594523115301722826252225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2126030820402297101669633 1594523115301722826252225)
                  ·
                    refine ⟨1195892336476292119689169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1594523115301722826252225 1195892336476292119689169)
                    ·
                      refine ⟨896919252357219089766877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195892336476292119689169 896919252357219089766877)
                      ·
                        rfl

theorem cell23_1746744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_1746744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746744 prefixEnd_1746744 := by exact prefixLift 1746744
  have htrace : WordTrace (prefixWord ++ tailWord_1746744) baseStart_1746744 baseEnd_1746744 := by
    simpa [prefixWord, tailWord_1746744, baseEnd_1746744] using wordTrace_append hprefix tailTrace_1746744
  have hstable : (prefixWord ++ tailWord_1746744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746744).length < 2 ^ (prefixWord ++ tailWord_1746744).sum := by decide
  have hdescent : baseEnd_1746744 < baseStart_1746744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746773 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1746773 : Nat := 118140960795 + 1746773 * 2 ^ 59
def prefixEnd_1746773 : Nat := 4983230072969 + 3 ^ 40 * 1746773 * 2
def baseEnd_1746773 : Nat := 896934143296199476304243

theorem tailTrace_1746773 : CollatzResearch.WordTrace tailWord_1746773 prefixEnd_1746773 896934143296199476304243 := by
  unfold tailWord_1746773
  simp only [CollatzResearch.WordTrace]
  refine ⟨63710045300747220922636973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42473363533831480615091315 63710045300747220922636973)
  ·
    refine ⟨23891266987780207845988865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63710045300747220922636973 23891266987780207845988865)
    ·
      refine ⟨17918450240835155884491649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23891266987780207845988865 17918450240835155884491649)
      ·
        refine ⟨13438837680626366913368737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17918450240835155884491649 13438837680626366913368737)
        ·
          refine ⟨10079128260469775185026553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13438837680626366913368737 10079128260469775185026553)
          ·
            refine ⟨7559346195352331388769915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10079128260469775185026553 7559346195352331388769915)
            ·
              refine ⟨11339019293028497083154873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7559346195352331388769915 11339019293028497083154873)
              ·
                refine ⟨8504264469771372812366155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11339019293028497083154873 8504264469771372812366155)
                ·
                  refine ⟨12756396704657059218549233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8504264469771372812366155 12756396704657059218549233)
                  ·
                    refine ⟨9567297528492794413911925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12756396704657059218549233 9567297528492794413911925)
                    ·
                      refine ⟨896934143296199476304243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9567297528492794413911925 896934143296199476304243)
                      ·
                        rfl

theorem cell23_1746773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1746773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746773 prefixEnd_1746773 := by exact prefixLift 1746773
  have htrace : WordTrace (prefixWord ++ tailWord_1746773) baseStart_1746773 baseEnd_1746773 := by
    simpa [prefixWord, tailWord_1746773, baseEnd_1746773] using wordTrace_append hprefix tailTrace_1746773
  have hstable : (prefixWord ++ tailWord_1746773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746773).length < 2 ^ (prefixWord ++ tailWord_1746773).sum := by decide
  have hdescent : baseEnd_1746773 < baseStart_1746773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746793 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 7, 4]
def baseStart_1746793 : Nat := 118140960795 + 1746793 * 2 ^ 59
def prefixEnd_1746793 : Nat := 4983230072969 + 3 ^ 40 * 1746793 * 2
def baseEnd_1746793 : Nat := 298981470969763132684717

theorem tailTrace_1746793 : CollatzResearch.WordTrace tailWord_1746793 prefixEnd_1746793 298981470969763132684717 := by
  unfold tailWord_1746793
  simp only [CollatzResearch.WordTrace]
  refine ⟨63710774760674764338365033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42473849840449842892243355 63710774760674764338365033)
  ·
    refine ⟨47783081070506073253773775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63710774760674764338365033 47783081070506073253773775)
    ·
      refine ⟨71674621605759109880660663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47783081070506073253773775 71674621605759109880660663)
      ·
        refine ⟨107511932408638664820990995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71674621605759109880660663 107511932408638664820990995)
        ·
          refine ⟨161267898612957997231486493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107511932408638664820990995 161267898612957997231486493)
          ·
            refine ⟨60475461979859248961807435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161267898612957997231486493 60475461979859248961807435)
            ·
              refine ⟨90713192969788873442711153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60475461979859248961807435 90713192969788873442711153)
              ·
                refine ⟨68034894727341655082033365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90713192969788873442711153 68034894727341655082033365)
                ·
                  refine ⟨1594567845172070040985157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 68034894727341655082033365 1594567845172070040985157)
                  ·
                    refine ⟨298981470969763132684717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1594567845172070040985157 298981470969763132684717)
                    ·
                      rfl

theorem cell23_1746793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_1746793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746793 prefixEnd_1746793 := by exact prefixLift 1746793
  have htrace : WordTrace (prefixWord ++ tailWord_1746793) baseStart_1746793 baseEnd_1746793 := by
    simpa [prefixWord, tailWord_1746793, baseEnd_1746793] using wordTrace_append hprefix tailTrace_1746793
  have hstable : (prefixWord ++ tailWord_1746793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746793).length < 2 ^ (prefixWord ++ tailWord_1746793).sum := by decide
  have hdescent : baseEnd_1746793 < baseStart_1746793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746803 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 3]
def baseStart_1746803 : Nat := 118140960795 + 1746803 * 2 ^ 59
def prefixEnd_1746803 : Nat := 4983230072969 + 3 ^ 40 * 1746803 * 2
def baseEnd_1746803 : Nat := 896949547715834358929105

theorem tailTrace_1746803 : CollatzResearch.WordTrace tailWord_1746803 prefixEnd_1746803 896949547715834358929105 := by
  unfold tailWord_1746803
  simp only [CollatzResearch.WordTrace]
  refine ⟨63711139490638536046229063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42474092993759024030819375 63711139490638536046229063)
  ·
    refine ⟨95566709235957804069343595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63711139490638536046229063 95566709235957804069343595)
    ·
      refine ⟨143350063853936706104015393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95566709235957804069343595 143350063853936706104015393)
      ·
        refine ⟨107512547890452529578011545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143350063853936706104015393 107512547890452529578011545)
        ·
          refine ⟨80634410917839397183508659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107512547890452529578011545 80634410917839397183508659)
          ·
            refine ⟨120951616376759095775262989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80634410917839397183508659 120951616376759095775262989)
            ·
              refine ⟨45356856141284660915723621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120951616376759095775262989 45356856141284660915723621)
              ·
                refine ⟨8504410526490873921698179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45356856141284660915723621 8504410526490873921698179)
                ·
                  refine ⟨12756615789736310882547269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8504410526490873921698179 12756615789736310882547269)
                  ·
                    refine ⟨2391865460575558290477613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12756615789736310882547269 2391865460575558290477613)
                    ·
                      refine ⟨896949547715834358929105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2391865460575558290477613 896949547715834358929105)
                      ·
                        rfl

theorem cell23_1746803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_1746803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746803 prefixEnd_1746803 := by exact prefixLift 1746803
  have htrace : WordTrace (prefixWord ++ tailWord_1746803) baseStart_1746803 baseEnd_1746803 := by
    simpa [prefixWord, tailWord_1746803, baseEnd_1746803] using wordTrace_append hprefix tailTrace_1746803
  have hstable : (prefixWord ++ tailWord_1746803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746803).length < 2 ^ (prefixWord ++ tailWord_1746803).sum := by decide
  have hdescent : baseEnd_1746803 < baseStart_1746803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746814 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1746814 : Nat := 118140960795 + 1746814 * 2 ^ 59
def prefixEnd_1746814 : Nat := 4983230072969 + 3 ^ 40 * 1746814 * 2
def baseEnd_1746814 : Nat := 298985065334344605297185

theorem tailTrace_1746814 : CollatzResearch.WordTrace tailWord_1746814 prefixEnd_1746814 298985065334344605297185 := by
  unfold tailWord_1746814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963942586699835615609937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42474360462399123283252997 7963942586699835615609937)
  ·
    refine ⟨5972956940024876711707453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7963942586699835615609937 5972956940024876711707453)
    ·
      refine ⟨2239858852509328766890295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5972956940024876711707453 2239858852509328766890295)
      ·
        refine ⟨3359788278763993150335443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239858852509328766890295 3359788278763993150335443)
        ·
          refine ⟨5039682418145989725503165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359788278763993150335443 5039682418145989725503165)
          ·
            refine ⟨1889880906804746147063687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5039682418145989725503165 1889880906804746147063687)
            ·
              refine ⟨2834821360207119220595531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889880906804746147063687 2834821360207119220595531)
              ·
                refine ⟨4252232040310678830893297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834821360207119220595531 4252232040310678830893297)
                ·
                  refine ⟨3189174030233009123169973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4252232040310678830893297 3189174030233009123169973)
                  ·
                    refine ⟨298985065334344605297185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3189174030233009123169973 298985065334344605297185)
                    ·
                      rfl

theorem cell23_1746814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1746814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746814 prefixEnd_1746814 := by exact prefixLift 1746814
  have htrace : WordTrace (prefixWord ++ tailWord_1746814) baseStart_1746814 baseEnd_1746814 := by
    simpa [prefixWord, tailWord_1746814, baseEnd_1746814] using wordTrace_append hprefix tailTrace_1746814
  have hstable : (prefixWord ++ tailWord_1746814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746814).length < 2 ^ (prefixWord ++ tailWord_1746814).sum := by decide
  have hdescent : baseEnd_1746814 < baseStart_1746814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746817 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1746817 : Nat := 118140960795 + 1746817 * 2 ^ 59
def prefixEnd_1746817 : Nat := 4983230072969 + 3 ^ 40 * 1746817 * 2
def baseEnd_1746817 : Nat := 896956736444997304154041

theorem tailTrace_1746817 : CollatzResearch.WordTrace tailWord_1746817 prefixEnd_1746817 896956736444997304154041 := by
  unfold tailWord_1746817
  simp only [CollatzResearch.WordTrace]
  refine ⟨63711650112587816437238705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42474433408391877624825803 63711650112587816437238705)
  ·
    refine ⟨47783737584440862327929029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63711650112587816437238705 47783737584440862327929029)
    ·
      refine ⟨8959450797082661686486693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47783737584440862327929029 8959450797082661686486693)
      ·
        refine ⟨1679897024452999066216255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8959450797082661686486693 1679897024452999066216255)
        ·
          refine ⟨2519845536679498599324383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679897024452999066216255 2519845536679498599324383)
          ·
            refine ⟨3779768305019247898986575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519845536679498599324383 3779768305019247898986575)
            ·
              refine ⟨5669652457528871848479863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779768305019247898986575 5669652457528871848479863)
              ·
                refine ⟨8504478686293307772719795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669652457528871848479863 8504478686293307772719795)
                ·
                  refine ⟨12756718029439961659079693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8504478686293307772719795 12756718029439961659079693)
                  ·
                    refine ⟨4783769261039985622154885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12756718029439961659079693 4783769261039985622154885)
                    ·
                      refine ⟨896956736444997304154041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4783769261039985622154885 896956736444997304154041)
                      ·
                        rfl

theorem cell23_1746817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1746817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746817 prefixEnd_1746817 := by exact prefixLift 1746817
  have htrace : WordTrace (prefixWord ++ tailWord_1746817) baseStart_1746817 baseEnd_1746817 := by
    simpa [prefixWord, tailWord_1746817, baseEnd_1746817] using wordTrace_append hprefix tailTrace_1746817
  have hstable : (prefixWord ++ tailWord_1746817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746817).length < 2 ^ (prefixWord ++ tailWord_1746817).sum := by decide
  have hdescent : baseEnd_1746817 < baseStart_1746817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746844 : List Nat := [2, 2, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1746844 : Nat := 118140960795 + 1746844 * 2 ^ 59
def prefixEnd_1746844 : Nat := 4983230072969 + 3 ^ 40 * 1746844 * 2
def baseEnd_1746844 : Nat := 298990200140889566172139

theorem tailTrace_1746844 : CollatzResearch.WordTrace tailWord_1746844 prefixEnd_1746844 298990200140889566172139 := by
  unfold tailWord_1746844
  simp only [CollatzResearch.WordTrace]
  refine ⟨31856317441745000024235793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42475089922326666698981057 31856317441745000024235793)
  ·
    refine ⟨23892238081308750018176845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31856317441745000024235793 23892238081308750018176845)
    ·
      refine ⟨8959589280490781256816317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23892238081308750018176845 8959589280490781256816317)
      ·
        refine ⟨3359845980184042971306119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8959589280490781256816317 3359845980184042971306119)
        ·
          refine ⟨5039768970276064456959179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359845980184042971306119 5039768970276064456959179)
          ·
            refine ⟨7559653455414096685438769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039768970276064456959179 7559653455414096685438769)
            ·
              refine ⟨5669740091560572514079077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559653455414096685438769 5669740091560572514079077)
              ·
                refine ⟨1063076267167607346389827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5669740091560572514079077 1063076267167607346389827)
                ·
                  refine ⟨1594614400751411019584741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063076267167607346389827 1594614400751411019584741)
                  ·
                    refine ⟨298990200140889566172139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1594614400751411019584741 298990200140889566172139)
                    ·
                      rfl

theorem cell23_1746844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1746844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746844 prefixEnd_1746844 := by exact prefixLift 1746844
  have htrace : WordTrace (prefixWord ++ tailWord_1746844) baseStart_1746844 baseEnd_1746844 := by
    simpa [prefixWord, tailWord_1746844, baseEnd_1746844] using wordTrace_append hprefix tailTrace_1746844
  have hstable : (prefixWord ++ tailWord_1746844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746844).length < 2 ^ (prefixWord ++ tailWord_1746844).sum := by decide
  have hdescent : baseEnd_1746844 < baseStart_1746844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746853 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_1746853 : Nat := 118140960795 + 1746853 * 2 ^ 59
def prefixEnd_1746853 : Nat := 4983230072969 + 3 ^ 40 * 1746853 * 2
def baseEnd_1746853 : Nat := 298991740582853054434625

theorem tailTrace_1746853 : CollatzResearch.WordTrace tailWord_1746853 prefixEnd_1746853 298991740582853054434625 := by
  unfold tailWord_1746853
  simp only [CollatzResearch.WordTrace]
  refine ⟨63712963140457394585549213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42475308760304929723699475 63712963140457394585549213)
  ·
    refine ⟨23892361177671522969580955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63712963140457394585549213 23892361177671522969580955)
    ·
      refine ⟨35838541766507284454371433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23892361177671522969580955 35838541766507284454371433)
      ·
        refine ⟨26878906324880463340778575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35838541766507284454371433 26878906324880463340778575)
        ·
          refine ⟨40318359487320695011167863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26878906324880463340778575 40318359487320695011167863)
          ·
            refine ⟨60477539230981042516751795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40318359487320695011167863 60477539230981042516751795)
            ·
              refine ⟨90716308846471563775127693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60477539230981042516751795 90716308846471563775127693)
              ·
                refine ⟨34018615817426836415672885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90716308846471563775127693 34018615817426836415672885)
                ·
                  refine ⟨3189245232883765913969333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34018615817426836415672885 3189245232883765913969333)
                  ·
                    refine ⟨298991740582853054434625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3189245232883765913969333 298991740582853054434625)
                    ·
                      rfl

theorem cell23_1746853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_1746853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746853 prefixEnd_1746853 := by exact prefixLift 1746853
  have htrace : WordTrace (prefixWord ++ tailWord_1746853) baseStart_1746853 baseEnd_1746853 := by
    simpa [prefixWord, tailWord_1746853, baseEnd_1746853] using wordTrace_append hprefix tailTrace_1746853
  have hstable : (prefixWord ++ tailWord_1746853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746853).length < 2 ^ (prefixWord ++ tailWord_1746853).sum := by decide
  have hdescent : baseEnd_1746853 < baseStart_1746853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746877 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_1746877 : Nat := 118140960795 + 1746877 * 2 ^ 59
def prefixEnd_1746877 : Nat := 4983230072969 + 3 ^ 40 * 1746877 * 2
def baseEnd_1746877 : Nat := 896987545284267069403765

theorem tailTrace_1746877 : CollatzResearch.WordTrace tailWord_1746877 prefixEnd_1746877 896987545284267069403765 := by
  unfold tailWord_1746877
  simp only [CollatzResearch.WordTrace]
  refine ⟨63713838492370446684422885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42475892328246964456281923 63713838492370446684422885)
  ·
    refine ⟨11946344717319458753329291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63713838492370446684422885 11946344717319458753329291)
    ·
      refine ⟨17919517075979188129993937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11946344717319458753329291 17919517075979188129993937)
      ·
        refine ⟨13439637806984391097495453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17919517075979188129993937 13439637806984391097495453)
        ·
          refine ⟨5039864177619146661560795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13439637806984391097495453 5039864177619146661560795)
          ·
            refine ⟨7559796266428719992341193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039864177619146661560795 7559796266428719992341193)
            ·
              refine ⟨5669847199821539994255895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559796266428719992341193 5669847199821539994255895)
              ·
                refine ⟨8504770799732309991383843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669847199821539994255895 8504770799732309991383843)
                ·
                  refine ⟨12757156199598464987075765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8504770799732309991383843 12757156199598464987075765)
                  ·
                    refine ⟨1195983393712356092538353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12757156199598464987075765 1195983393712356092538353)
                    ·
                      refine ⟨896987545284267069403765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1195983393712356092538353 896987545284267069403765)
                      ·
                        rfl

theorem cell23_1746877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_1746877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746877 prefixEnd_1746877 := by exact prefixLift 1746877
  have htrace : WordTrace (prefixWord ++ tailWord_1746877) baseStart_1746877 baseEnd_1746877 := by
    simpa [prefixWord, tailWord_1746877, baseEnd_1746877] using wordTrace_append hprefix tailTrace_1746877
  have hstable : (prefixWord ++ tailWord_1746877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746877).length < 2 ^ (prefixWord ++ tailWord_1746877).sum := by decide
  have hdescent : baseEnd_1746877 < baseStart_1746877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746903 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1746903 : Nat := 118140960795 + 1746903 * 2 ^ 59
def prefixEnd_1746903 : Nat := 4983230072969 + 3 ^ 40 * 1746903 * 2
def baseEnd_1746903 : Nat := 897000895781283967678645

theorem tailTrace_1746903 : CollatzResearch.WordTrace tailWord_1746903 prefixEnd_1746903 897000895781283967678645 := by
  unfold tailWord_1746903
  simp only [CollatzResearch.WordTrace]
  refine ⟨63714786790276253124869363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42476524526850835416579575 63714786790276253124869363)
  ·
    refine ⟨95572180185414379687304045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63714786790276253124869363 95572180185414379687304045)
    ·
      refine ⟨35839567569530392382739017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95572180185414379687304045 35839567569530392382739017)
      ·
        refine ⟨26879675677147794287054263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35839567569530392382739017 26879675677147794287054263)
        ·
          refine ⟨40319513515721691430581395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26879675677147794287054263 40319513515721691430581395)
          ·
            refine ⟨60479270273582537145872093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40319513515721691430581395 60479270273582537145872093)
            ·
              refine ⟨22679726352593451429702035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60479270273582537145872093 22679726352593451429702035)
              ·
                refine ⟨34019589528890177144553053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22679726352593451429702035 34019589528890177144553053)
                ·
                  refine ⟨12757346073333816429207395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34019589528890177144553053 12757346073333816429207395)
                  ·
                    refine ⟨19136019110000724643811093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12757346073333816429207395 19136019110000724643811093)
                    ·
                      refine ⟨897000895781283967678645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19136019110000724643811093 897000895781283967678645)
                      ·
                        rfl

theorem cell23_1746903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1746903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746903 prefixEnd_1746903 := by exact prefixLift 1746903
  have htrace : WordTrace (prefixWord ++ tailWord_1746903) baseStart_1746903 baseEnd_1746903 := by
    simpa [prefixWord, tailWord_1746903, baseEnd_1746903] using wordTrace_append hprefix tailTrace_1746903
  have hstable : (prefixWord ++ tailWord_1746903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746903).length < 2 ^ (prefixWord ++ tailWord_1746903).sum := by decide
  have hdescent : baseEnd_1746903 < baseStart_1746903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746908 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 6]
def baseStart_1746908 : Nat := 118140960795 + 1746908 * 2 ^ 59
def prefixEnd_1746908 : Nat := 4983230072969 + 3 ^ 40 * 1746908 * 2
def baseEnd_1746908 : Nat := 99667051464950716457347

theorem tailTrace_1746908 : CollatzResearch.WordTrace tailWord_1746908 prefixEnd_1746908 99667051464950716457347 := by
  unfold tailWord_1746908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31857484577629069489400689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42476646103505425985867585 31857484577629069489400689)
  ·
    refine ⟨23893113433221802117050517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31857484577629069489400689 23893113433221802117050517)
    ·
      refine ⟨1119989692182271974236743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23893113433221802117050517 1119989692182271974236743)
      ·
        refine ⟨1679984538273407961355115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119989692182271974236743 1679984538273407961355115)
        ·
          refine ⟨2519976807410111942032673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679984538273407961355115 2519976807410111942032673)
          ·
            refine ⟨1889982605557583956524505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2519976807410111942032673 1889982605557583956524505)
            ·
              refine ⟨1417486954168187967393379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889982605557583956524505 1417486954168187967393379)
              ·
                refine ⟨2126230431252281951090069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417486954168187967393379 2126230431252281951090069)
                ·
                  refine ⟨99667051464950716457347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2126230431252281951090069 99667051464950716457347)
                  ·
                    rfl

theorem cell23_1746908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_1746908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746908 prefixEnd_1746908 := by exact prefixLift 1746908
  have htrace : WordTrace (prefixWord ++ tailWord_1746908) baseStart_1746908 baseEnd_1746908 := by
    simpa [prefixWord, tailWord_1746908, baseEnd_1746908] using wordTrace_append hprefix tailTrace_1746908
  have hstable : (prefixWord ++ tailWord_1746908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746908).length < 2 ^ (prefixWord ++ tailWord_1746908).sum := by decide
  have hdescent : baseEnd_1746908 < baseStart_1746908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746913 : List Nat := [1, 2, 3, 1, 2, 1, 3, 10]
def baseStart_1746913 : Nat := 118140960795 + 1746913 * 2 ^ 59
def prefixEnd_1746913 : Nat := 4983230072969 + 3 ^ 40 * 1746913 * 2
def baseEnd_1746913 : Nat := 33222445577326997353837

theorem tailTrace_1746913 : CollatzResearch.WordTrace tailWord_1746913 prefixEnd_1746913 33222445577326997353837 := by
  unfold tailWord_1746913
  simp only [CollatzResearch.WordTrace]
  refine ⟨63715151520240024832733393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42476767680160016555155595 63715151520240024832733393)
  ·
    refine ⟨47786363640180018624550045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63715151520240024832733393 47786363640180018624550045)
    ·
      refine ⟨17919886365067506984206267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47786363640180018624550045 17919886365067506984206267)
      ·
        refine ⟨26879829547601260476309401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17919886365067506984206267 26879829547601260476309401)
        ·
          refine ⟨20159872160700945357232051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26879829547601260476309401 20159872160700945357232051)
          ·
            refine ⟨30239808241051418035848077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20159872160700945357232051 30239808241051418035848077)
            ·
              refine ⟨11339928090394281763443029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30239808241051418035848077 11339928090394281763443029)
              ·
                refine ⟨33222445577326997353837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11339928090394281763443029 33222445577326997353837)
                ·
                  rfl

theorem cell23_1746913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 10].length) (baseStart_1746913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746913 prefixEnd_1746913 := by exact prefixLift 1746913
  have htrace : WordTrace (prefixWord ++ tailWord_1746913) baseStart_1746913 baseEnd_1746913 := by
    simpa [prefixWord, tailWord_1746913, baseEnd_1746913] using wordTrace_append hprefix tailTrace_1746913
  have hstable : (prefixWord ++ tailWord_1746913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746913).length < 2 ^ (prefixWord ++ tailWord_1746913).sum := by decide
  have hdescent : baseEnd_1746913 < baseStart_1746913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746920 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1746920 : Nat := 118140960795 + 1746920 * 2 ^ 59
def prefixEnd_1746920 : Nat := 4983230072969 + 3 ^ 40 * 1746920 * 2
def baseEnd_1746920 : Nat := 897009624952410401166067

theorem tailTrace_1746920 : CollatzResearch.WordTrace tailWord_1746920 prefixEnd_1746920 897009624952410401166067 := by
  unfold tailWord_1746920
  simp only [CollatzResearch.WordTrace]
  refine ⟨31857703415607332514119107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42476937887476443352158809 31857703415607332514119107)
  ·
    refine ⟨47786555123410998771178661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31857703415607332514119107 47786555123410998771178661)
    ·
      refine ⟨8959979085639562269595999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47786555123410998771178661 8959979085639562269595999)
      ·
        refine ⟨13439968628459343404393999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8959979085639562269595999 13439968628459343404393999)
        ·
          refine ⟨20159952942689015106590999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13439968628459343404393999 20159952942689015106590999)
          ·
            refine ⟨30239929414033522659886499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20159952942689015106590999 30239929414033522659886499)
            ·
              refine ⟨45359894121050283989829749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30239929414033522659886499 45359894121050283989829749)
              ·
                refine ⟨4252490073848464124046539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45359894121050283989829749 4252490073848464124046539)
                ·
                  refine ⟨6378735110772696186069809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252490073848464124046539 6378735110772696186069809)
                  ·
                    refine ⟨4784051333079522139552357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6378735110772696186069809 4784051333079522139552357)
                    ·
                      refine ⟨897009624952410401166067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4784051333079522139552357 897009624952410401166067)
                      ·
                        rfl

theorem cell23_1746920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1746920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746920 prefixEnd_1746920 := by exact prefixLift 1746920
  have htrace : WordTrace (prefixWord ++ tailWord_1746920) baseStart_1746920 baseEnd_1746920 := by
    simpa [prefixWord, tailWord_1746920, baseEnd_1746920] using wordTrace_append hprefix tailTrace_1746920
  have hstable : (prefixWord ++ tailWord_1746920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746920).length < 2 ^ (prefixWord ++ tailWord_1746920).sum := by decide
  have hdescent : baseEnd_1746920 < baseStart_1746920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746943 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 4, 7]
def baseStart_1746943 : Nat := 118140960795 + 1746943 * 2 ^ 59
def prefixEnd_1746943 : Nat := 4983230072969 + 3 ^ 40 * 1746943 * 2
def baseEnd_1746943 : Nat := 299007145002487937059487

theorem tailTrace_1746943 : CollatzResearch.WordTrace tailWord_1746943 prefixEnd_1746943 299007145002487937059487 := by
  unfold tailWord_1746943
  simp only [CollatzResearch.WordTrace]
  refine ⟨63716245710131339956325483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42477497140087559970883655 63716245710131339956325483)
  ·
    refine ⟨95574368565197009934488225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63716245710131339956325483 95574368565197009934488225)
    ·
      refine ⟨71680776423897757450866169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95574368565197009934488225 71680776423897757450866169)
      ·
        refine ⟨53760582317923318088149627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71680776423897757450866169 53760582317923318088149627)
        ·
          refine ⟨80640873476884977132224441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53760582317923318088149627 80640873476884977132224441)
          ·
            refine ⟨60480655107663732849168331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80640873476884977132224441 60480655107663732849168331)
            ·
              refine ⟨90720982661495599273752497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60480655107663732849168331 90720982661495599273752497)
              ·
                refine ⟨68040736996121699455314373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90720982661495599273752497 68040736996121699455314373)
                ·
                  refine ⟨12757638186772818647871445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68040736996121699455314373 12757638186772818647871445)
                  ·
                    refine ⟨299007145002487937059487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12757638186772818647871445 299007145002487937059487)
                    ·
                      rfl

theorem cell23_1746943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_1746943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746943 prefixEnd_1746943 := by exact prefixLift 1746943
  have htrace : WordTrace (prefixWord ++ tailWord_1746943) baseStart_1746943 baseEnd_1746943 := by
    simpa [prefixWord, tailWord_1746943, baseEnd_1746943] using wordTrace_append hprefix tailTrace_1746943
  have hstable : (prefixWord ++ tailWord_1746943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746943).length < 2 ^ (prefixWord ++ tailWord_1746943).sum := by decide
  have hdescent : baseEnd_1746943 < baseStart_1746943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746953 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_1746953 : Nat := 118140960795 + 1746953 * 2 ^ 59
def prefixEnd_1746953 : Nat := 4983230072969 + 3 ^ 40 * 1746953 * 2
def baseEnd_1746953 : Nat := 897026569814008772053415

theorem tailTrace_1746953 : CollatzResearch.WordTrace tailWord_1746953 prefixEnd_1746953 897026569814008772053415 := by
  unfold tailWord_1746953
  simp only [CollatzResearch.WordTrace]
  refine ⟨63716610440095111664189513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42477740293396741109459675 63716610440095111664189513)
  ·
    refine ⟨47787457830071333748142135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63716610440095111664189513 47787457830071333748142135)
    ·
      refine ⟨71681186745107000622213203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47787457830071333748142135 71681186745107000622213203)
      ·
        refine ⟨107521780117660500933319805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71681186745107000622213203 107521780117660500933319805)
        ·
          refine ⟨40320667544122687849994927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107521780117660500933319805 40320667544122687849994927)
          ·
            refine ⟨60481001316184031774992391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40320667544122687849994927 60481001316184031774992391)
            ·
              refine ⟨90721501974276047662488587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60481001316184031774992391 90721501974276047662488587)
              ·
                refine ⟨136082252961414071493732881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90721501974276047662488587 136082252961414071493732881)
                ·
                  refine ⟨102061689721060553620299661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136082252961414071493732881 102061689721060553620299661)
                  ·
                    refine ⟨38273133645397707607612373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102061689721060553620299661 38273133645397707607612373)
                    ·
                      refine ⟨897026569814008772053415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38273133645397707607612373 897026569814008772053415)
                      ·
                        rfl

theorem cell23_1746953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_1746953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1746953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1746953 prefixEnd_1746953 := by exact prefixLift 1746953
  have htrace : WordTrace (prefixWord ++ tailWord_1746953) baseStart_1746953 baseEnd_1746953 := by
    simpa [prefixWord, tailWord_1746953, baseEnd_1746953] using wordTrace_append hprefix tailTrace_1746953
  have hstable : (prefixWord ++ tailWord_1746953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746953).length < 2 ^ (prefixWord ++ tailWord_1746953).sum := by decide
  have hdescent : baseEnd_1746953 < baseStart_1746953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747001 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1747001 : Nat := 118140960795 + 1747001 * 2 ^ 59
def prefixEnd_1747001 : Nat := 4983230072969 + 3 ^ 40 * 1747001 * 2
def baseEnd_1747001 : Nat := 897051216885424584253195

theorem tailTrace_1747001 : CollatzResearch.WordTrace tailWord_1747001 prefixEnd_1747001 897051216885424584253195 := by
  unfold tailWord_1747001
  simp only [CollatzResearch.WordTrace]
  refine ⟨63718361143921215861936857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42478907429280810574624571 63718361143921215861936857)
  ·
    refine ⟨47788770857940911896452643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63718361143921215861936857 47788770857940911896452643)
    ·
      refine ⟨71683156286911367844678965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47788770857940911896452643 71683156286911367844678965)
      ·
        refine ⟨6720295901897940735438653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71683156286911367844678965 6720295901897940735438653)
        ·
          refine ⟨2520110963211727775789495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6720295901897940735438653 2520110963211727775789495)
          ·
            refine ⟨3780166444817591663684243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520110963211727775789495 3780166444817591663684243)
            ·
              refine ⟨5670249667226387495526365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780166444817591663684243 5670249667226387495526365)
              ·
                refine ⟨2126343625209895310822387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5670249667226387495526365 2126343625209895310822387)
                ·
                  refine ⟨3189515437814842966233581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126343625209895310822387 3189515437814842966233581)
                  ·
                    refine ⟨1196068289180566112337593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189515437814842966233581 1196068289180566112337593)
                    ·
                      refine ⟨897051216885424584253195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196068289180566112337593 897051216885424584253195)
                      ·
                        rfl

theorem cell23_1747001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1747001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747001 prefixEnd_1747001 := by exact prefixLift 1747001
  have htrace : WordTrace (prefixWord ++ tailWord_1747001) baseStart_1747001 baseEnd_1747001 := by
    simpa [prefixWord, tailWord_1747001, baseEnd_1747001] using wordTrace_append hprefix tailTrace_1747001
  have hstable : (prefixWord ++ tailWord_1747001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747001).length < 2 ^ (prefixWord ++ tailWord_1747001).sum := by decide
  have hdescent : baseEnd_1747001 < baseStart_1747001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747020 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 7]
def baseStart_1747020 : Nat := 118140960795 + 1747020 * 2 ^ 59
def prefixEnd_1747020 : Nat := 4983230072969 + 3 ^ 40 * 1747020 * 2
def baseEnd_1747020 : Nat := 99673441446428889990623

theorem tailTrace_1747020 : CollatzResearch.WordTrace tailWord_1747020 prefixEnd_1747020 99673441446428889990623 := by
  unfold tailWord_1747020
  simp only [CollatzResearch.WordTrace]
  refine ⟨31859527065426191053439257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42479369420568254737919009 31859527065426191053439257)
  ·
    refine ⟨23894645299069643290079443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31859527065426191053439257 23894645299069643290079443)
    ·
      refine ⟨35841967948604464935119165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23894645299069643290079443 35841967948604464935119165)
      ·
        refine ⟨13440737980726674350669687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35841967948604464935119165 13440737980726674350669687)
        ·
          refine ⟨20161106971090011526004531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13440737980726674350669687 20161106971090011526004531)
          ·
            refine ⟨30241660456635017289006797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20161106971090011526004531 30241660456635017289006797)
            ·
              refine ⟨11340622671238131483377549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30241660456635017289006797 11340622671238131483377549)
              ·
                refine ⟨4252733501714299306266581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11340622671238131483377549 4252733501714299306266581)
                ·
                  refine ⟨99673441446428889990623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4252733501714299306266581 99673441446428889990623)
                  ·
                    rfl

theorem cell23_1747020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_1747020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747020 prefixEnd_1747020 := by exact prefixLift 1747020
  have htrace : WordTrace (prefixWord ++ tailWord_1747020) baseStart_1747020 baseEnd_1747020 := by
    simpa [prefixWord, tailWord_1747020, baseEnd_1747020] using wordTrace_append hprefix tailTrace_1747020
  have hstable : (prefixWord ++ tailWord_1747020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747020).length < 2 ^ (prefixWord ++ tailWord_1747020).sum := by decide
  have hdescent : baseEnd_1747020 < baseStart_1747020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747077 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_1747077 : Nat := 118140960795 + 1747077 * 2 ^ 59
def prefixEnd_1747077 : Nat := 4983230072969 + 3 ^ 40 * 1747077 * 2
def baseEnd_1747077 : Nat := 897090241415166286902845

theorem tailTrace_1747077 : CollatzResearch.WordTrace tailWord_1747077 prefixEnd_1747077 897090241415166286902845 := by
  unfold tailWord_1747077
  simp only [CollatzResearch.WordTrace]
  refine ⟨63721133091645880841703485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42480755394430587227802323 63721133091645880841703485)
  ·
    refine ⟨23895424909367205315638807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63721133091645880841703485 23895424909367205315638807)
    ·
      refine ⟨35843137364050807973458211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23895424909367205315638807 35843137364050807973458211)
      ·
        refine ⟨53764706046076211960187317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35843137364050807973458211 53764706046076211960187317)
        ·
          refine ⟨5040441191819644871267561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53764706046076211960187317 5040441191819644871267561)
          ·
            refine ⟨3780330893864733653450671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5040441191819644871267561 3780330893864733653450671)
            ·
              refine ⟨5670496340797100480176007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780330893864733653450671 5670496340797100480176007)
              ·
                refine ⟨8505744511195650720264011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670496340797100480176007 8505744511195650720264011)
                ·
                  refine ⟨12758616766793476080396017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8505744511195650720264011 12758616766793476080396017)
                  ·
                    refine ⟨9568962575095107060297013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12758616766793476080396017 9568962575095107060297013)
                    ·
                      refine ⟨897090241415166286902845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9568962575095107060297013 897090241415166286902845)
                      ·
                        rfl

theorem cell23_1747077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_1747077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747077 prefixEnd_1747077 := by exact prefixLift 1747077
  have htrace : WordTrace (prefixWord ++ tailWord_1747077) baseStart_1747077 baseEnd_1747077 := by
    simpa [prefixWord, tailWord_1747077, baseEnd_1747077] using wordTrace_append hprefix tailTrace_1747077
  have hstable : (prefixWord ++ tailWord_1747077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747077).length < 2 ^ (prefixWord ++ tailWord_1747077).sum := by decide
  have hdescent : baseEnd_1747077 < baseStart_1747077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747097 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 3, 4]
def baseStart_1747097 : Nat := 118140960795 + 1747097 * 2 ^ 59
def prefixEnd_1747097 : Nat := 4983230072969 + 3 ^ 40 * 1747097 * 2
def baseEnd_1747097 : Nat := 299033503676085402884251

theorem tailTrace_1747097 : CollatzResearch.WordTrace tailWord_1747097 prefixEnd_1747097 299033503676085402884251 := by
  unfold tailWord_1747097
  simp only [CollatzResearch.WordTrace]
  refine ⟨63721862551573424257431545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42481241701048949504954363 63721862551573424257431545)
  ·
    refine ⟨47791396913680068193073659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63721862551573424257431545 47791396913680068193073659)
    ·
      refine ⟨71687095370520102289610489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47791396913680068193073659 71687095370520102289610489)
      ·
        refine ⟨53765321527890076717207867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71687095370520102289610489 53765321527890076717207867)
        ·
          refine ⟨80647982291835115075811801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53765321527890076717207867 80647982291835115075811801)
          ·
            refine ⟨60485986718876336306858851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80647982291835115075811801 60485986718876336306858851)
            ·
              refine ⟨90728980078314504460288277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60485986718876336306858851 90728980078314504460288277)
              ·
                refine ⟨4252920941170992396576013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90728980078314504460288277 4252920941170992396576013)
                ·
                  refine ⟨1594845352939122148716005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4252920941170992396576013 1594845352939122148716005)
                  ·
                    refine ⟨299033503676085402884251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1594845352939122148716005 299033503676085402884251)
                    ·
                      rfl

theorem cell23_1747097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_1747097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747097 prefixEnd_1747097 := by exact prefixLift 1747097
  have htrace : WordTrace (prefixWord ++ tailWord_1747097) baseStart_1747097 baseEnd_1747097 := by
    simpa [prefixWord, tailWord_1747097, baseEnd_1747097] using wordTrace_append hprefix tailTrace_1747097
  have hstable : (prefixWord ++ tailWord_1747097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747097).length < 2 ^ (prefixWord ++ tailWord_1747097).sum := by decide
  have hdescent : baseEnd_1747097 < baseStart_1747097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747104 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1747104 : Nat := 118140960795 + 1747104 * 2 ^ 59
def prefixEnd_1747104 : Nat := 4983230072969 + 3 ^ 40 * 1747104 * 2
def baseEnd_1747104 : Nat := 897104105392837681265221

theorem tailTrace_1747104 : CollatzResearch.WordTrace tailWord_1747104 prefixEnd_1747104 897104105392837681265221 := by
  unfold tailWord_1747104
  simp only [CollatzResearch.WordTrace]
  refine ⟨31861058931274032226468183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42481411908365376301957577 31861058931274032226468183)
  ·
    refine ⟨47791588396911048339702275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31861058931274032226468183 47791588396911048339702275)
    ·
      refine ⟨71687382595366572509553413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47791588396911048339702275 71687382595366572509553413)
      ·
        refine ⟨13441384236631232345541265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71687382595366572509553413 13441384236631232345541265)
        ·
          refine ⟨10081038177473424259155949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13441384236631232345541265 10081038177473424259155949)
          ·
            refine ⟨3780389316552534097183481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10081038177473424259155949 3780389316552534097183481)
            ·
              refine ⟨2835291987414400572887611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780389316552534097183481 2835291987414400572887611)
              ·
                refine ⟨4252937981121600859331417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835291987414400572887611 4252937981121600859331417)
                ·
                  refine ⟨3189703485841200644498563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4252937981121600859331417 3189703485841200644498563)
                  ·
                    refine ⟨4784555228761800966747845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189703485841200644498563 4784555228761800966747845)
                    ·
                      refine ⟨897104105392837681265221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4784555228761800966747845 897104105392837681265221)
                      ·
                        rfl

theorem cell23_1747104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1747104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747104 prefixEnd_1747104 := by exact prefixLift 1747104
  have htrace : WordTrace (prefixWord ++ tailWord_1747104) baseStart_1747104 baseEnd_1747104 := by
    simpa [prefixWord, tailWord_1747104, baseEnd_1747104] using wordTrace_append hprefix tailTrace_1747104
  have hstable : (prefixWord ++ tailWord_1747104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747104).length < 2 ^ (prefixWord ++ tailWord_1747104).sum := by decide
  have hdescent : baseEnd_1747104 < baseStart_1747104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747127 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 6]
def baseStart_1747127 : Nat := 118140960795 + 1747127 * 2 ^ 59
def prefixEnd_1747127 : Nat := 4983230072969 + 3 ^ 40 * 1747127 * 2
def baseEnd_1747127 : Nat := 99679546160876787919735

theorem tailTrace_1747127 : CollatzResearch.WordTrace tailWord_1747127 prefixEnd_1747127 99679546160876787919735 := by
  unfold tailWord_1747127
  simp only [CollatzResearch.WordTrace]
  refine ⟨63722956741464739381023635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42481971160976492920682423 63722956741464739381023635)
  ·
    refine ⟨95584435112197109071535453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63722956741464739381023635 95584435112197109071535453)
    ·
      refine ⟨35844163167073915901825795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95584435112197109071535453 35844163167073915901825795)
      ·
        refine ⟨53766244750610873852738693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35844163167073915901825795 53766244750610873852738693)
        ·
          refine ⟨10081170890739538847388505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53766244750610873852738693 10081170890739538847388505)
          ·
            refine ⟨7560878168054654135541379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10081170890739538847388505 7560878168054654135541379)
            ·
              refine ⟨11341317252081981203312069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7560878168054654135541379 11341317252081981203312069)
              ·
                refine ⟨2126496984765371475621013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11341317252081981203312069 2126496984765371475621013)
                ·
                  refine ⟨99679546160876787919735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2126496984765371475621013 99679546160876787919735)
                  ·
                    rfl

theorem cell23_1747127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 6].length) (baseStart_1747127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747127 prefixEnd_1747127 := by exact prefixLift 1747127
  have htrace : WordTrace (prefixWord ++ tailWord_1747127) baseStart_1747127 baseEnd_1747127 := by
    simpa [prefixWord, tailWord_1747127, baseEnd_1747127] using wordTrace_append hprefix tailTrace_1747127
  have hstable : (prefixWord ++ tailWord_1747127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747127).length < 2 ^ (prefixWord ++ tailWord_1747127).sum := by decide
  have hdescent : baseEnd_1747127 < baseStart_1747127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747138 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_1747138 : Nat := 118140960795 + 1747138 * 2 ^ 59
def prefixEnd_1747138 : Nat := 4983230072969 + 3 ^ 40 * 1747138 * 2
def baseEnd_1747138 : Nat := 897121563735090548240065

theorem tailTrace_1747138 : CollatzResearch.WordTrace tailWord_1747138 prefixEnd_1747138 897121563735090548240065 := by
  unfold tailWord_1747138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15930839486106222064918517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42482238629616592173116045 15930839486106222064918517)
  ·
    refine ⟨1493516201822458318586111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15930839486106222064918517 1493516201822458318586111)
    ·
      refine ⟨2240274302733687477879167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493516201822458318586111 2240274302733687477879167)
      ·
        refine ⟨3360411454100531216818751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240274302733687477879167 3360411454100531216818751)
        ·
          refine ⟨5040617181150796825228127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360411454100531216818751 5040617181150796825228127)
          ·
            refine ⟨7560925771726195237842191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040617181150796825228127 7560925771726195237842191)
            ·
              refine ⟨11341388657589292856763287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7560925771726195237842191 11341388657589292856763287)
              ·
                refine ⟨17012082986383939285144931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11341388657589292856763287 17012082986383939285144931)
                ·
                  refine ⟨25518124479575908927717397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17012082986383939285144931 25518124479575908927717397)
                  ·
                    refine ⟨1196162084980120730986753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25518124479575908927717397 1196162084980120730986753)
                    ·
                      refine ⟨897121563735090548240065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196162084980120730986753 897121563735090548240065)
                      ·
                        rfl

theorem cell23_1747138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_1747138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747138 prefixEnd_1747138 := by exact prefixLift 1747138
  have htrace : WordTrace (prefixWord ++ tailWord_1747138) baseStart_1747138 baseEnd_1747138 := by
    simpa [prefixWord, tailWord_1747138, baseEnd_1747138] using wordTrace_append hprefix tailTrace_1747138
  have hstable : (prefixWord ++ tailWord_1747138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747138).length < 2 ^ (prefixWord ++ tailWord_1747138).sum := by decide
  have hdescent : baseEnd_1747138 < baseStart_1747138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747158 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1747158 : Nat := 118140960795 + 1747158 * 2 ^ 59
def prefixEnd_1747158 : Nat := 4983230072969 + 3 ^ 40 * 1747158 * 2
def baseEnd_1747158 : Nat := 897131833348180469989973

theorem tailTrace_1747158 : CollatzResearch.WordTrace tailWord_1747158 prefixEnd_1747158 897131833348180469989973 := by
  unfold tailWord_1747158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982755462772026979712633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42482724936234954450268085 3982755462772026979712633)
  ·
    refine ⟨2987066597079020234784475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3982755462772026979712633 2987066597079020234784475)
    ·
      refine ⟨4480599895618530352176713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987066597079020234784475 4480599895618530352176713)
      ·
        refine ⟨3360449921713897764132535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4480599895618530352176713 3360449921713897764132535)
        ·
          refine ⟨5040674882570846646198803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360449921713897764132535 5040674882570846646198803)
          ·
            refine ⟨7561012323856269969298205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040674882570846646198803 7561012323856269969298205)
            ·
              refine ⟨2835379621446101238486827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7561012323856269969298205 2835379621446101238486827)
              ·
                refine ⟨4253069432169151857730241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835379621446101238486827 4253069432169151857730241)
                ·
                  refine ⟨3189802074126863893297681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4253069432169151857730241 3189802074126863893297681)
                  ·
                    refine ⟨2392351555595147919973261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3189802074126863893297681 2392351555595147919973261)
                    ·
                      refine ⟨897131833348180469989973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392351555595147919973261 897131833348180469989973)
                      ·
                        rfl

theorem cell23_1747158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1747158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747158 prefixEnd_1747158 := by exact prefixLift 1747158
  have htrace : WordTrace (prefixWord ++ tailWord_1747158) baseStart_1747158 baseEnd_1747158 := by
    simpa [prefixWord, tailWord_1747158, baseEnd_1747158] using wordTrace_append hprefix tailTrace_1747158
  have hstable : (prefixWord ++ tailWord_1747158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747158).length < 2 ^ (prefixWord ++ tailWord_1747158).sum := by decide
  have hdescent : baseEnd_1747158 < baseStart_1747158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747211 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 3, 2, 2]
def baseStart_1747211 : Nat := 118140960795 + 1747211 * 2 ^ 59
def prefixEnd_1747211 : Nat := 4983230072969 + 3 ^ 40 * 1747211 * 2
def baseEnd_1747211 : Nat := 897159047822868762627229

theorem tailTrace_1747211 : CollatzResearch.WordTrace tailWord_1747211 prefixEnd_1747211 897159047822868762627229 := by
  unfold tailWord_1747211
  simp only [CollatzResearch.WordTrace]
  refine ⟨63726020473160421727081487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42484013648773614484720991 63726020473160421727081487)
  ·
    refine ⟨95589030709740632590622231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63726020473160421727081487 95589030709740632590622231)
    ·
      refine ⟨143383546064610948885933347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95589030709740632590622231 143383546064610948885933347)
      ·
        refine ⟨215075319096916423328900021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143383546064610948885933347 215075319096916423328900021)
        ·
          refine ⟨20163311165335914687084377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215075319096916423328900021 20163311165335914687084377)
          ·
            refine ⟨15122483374001936015313283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20163311165335914687084377 15122483374001936015313283)
            ·
              refine ⟨22683725061002904022969925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15122483374001936015313283 22683725061002904022969925)
              ·
                refine ⟨4253198448938044504306861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22683725061002904022969925 4253198448938044504306861)
                ·
                  refine ⟨1594949418351766689115073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4253198448938044504306861 1594949418351766689115073)
                  ·
                    refine ⟨1196212063763825016836305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1594949418351766689115073 1196212063763825016836305)
                    ·
                      refine ⟨897159047822868762627229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196212063763825016836305 897159047822868762627229)
                      ·
                        rfl

theorem cell23_1747211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 2, 2].length) (baseStart_1747211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747211 prefixEnd_1747211 := by exact prefixLift 1747211
  have htrace : WordTrace (prefixWord ++ tailWord_1747211) baseStart_1747211 baseEnd_1747211 := by
    simpa [prefixWord, tailWord_1747211, baseEnd_1747211] using wordTrace_append hprefix tailTrace_1747211
  have hstable : (prefixWord ++ tailWord_1747211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747211).length < 2 ^ (prefixWord ++ tailWord_1747211).sum := by decide
  have hdescent : baseEnd_1747211 < baseStart_1747211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747217 : List Nat := [1, 2, 2, 1, 1, 6, 1, 9]
def baseStart_1747217 : Nat := 118140960795 + 1747217 * 2 ^ 59
def prefixEnd_1747217 : Nat := 4983230072969 + 3 ^ 40 * 1747217 * 2
def baseEnd_1747217 : Nat := 33228226989140582931563

theorem tailTrace_1747217 : CollatzResearch.WordTrace tailWord_1747217 prefixEnd_1747217 33228226989140582931563 := by
  unfold tailWord_1747217
  simp only [CollatzResearch.WordTrace]
  refine ⟨63726239311138684751799905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42484159540759123167866603 63726239311138684751799905)
  ·
    refine ⟨47794679483354013563849929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63726239311138684751799905 47794679483354013563849929)
    ·
      refine ⟨35846009612515510172887447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47794679483354013563849929 35846009612515510172887447)
      ·
        refine ⟨53769014418773265259331171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35846009612515510172887447 53769014418773265259331171)
        ·
          refine ⟨80653521628159897888996757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53769014418773265259331171 80653521628159897888996757)
          ·
            refine ⟨3780633826319995213546723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80653521628159897888996757 3780633826319995213546723)
            ·
              refine ⟨5670950739479992820320085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780633826319995213546723 5670950739479992820320085)
              ·
                refine ⟨33228226989140582931563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5670950739479992820320085 33228226989140582931563)
                ·
                  rfl

theorem cell23_1747217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 9].length) (baseStart_1747217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747217 prefixEnd_1747217 := by exact prefixLift 1747217
  have htrace : WordTrace (prefixWord ++ tailWord_1747217) baseStart_1747217 baseEnd_1747217 := by
    simpa [prefixWord, tailWord_1747217, baseEnd_1747217] using wordTrace_append hprefix tailTrace_1747217
  have hstable : (prefixWord ++ tailWord_1747217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747217).length < 2 ^ (prefixWord ++ tailWord_1747217).sum := by decide
  have hdescent : baseEnd_1747217 < baseStart_1747217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747231 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 3]
def baseStart_1747231 : Nat := 118140960795 + 1747231 * 2 ^ 59
def prefixEnd_1747231 : Nat := 4983230072969 + 3 ^ 40 * 1747231 * 2
def baseEnd_1747231 : Nat := 897169317435958684377137

theorem tailTrace_1747231 : CollatzResearch.WordTrace tailWord_1747231 prefixEnd_1747231 897169317435958684377137 := by
  unfold tailWord_1747231
  simp only [CollatzResearch.WordTrace]
  refine ⟨63726749933087965142809547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42484499955391976761873031 63726749933087965142809547)
  ·
    refine ⟨95590124899631947714214321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63726749933087965142809547 95590124899631947714214321)
    ·
      refine ⟨71692593674723960785660741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95590124899631947714214321 71692593674723960785660741)
      ·
        refine ⟨13442361314010742647311389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71692593674723960785660741 13442361314010742647311389)
        ·
          refine ⟨5040885492754028492741771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13442361314010742647311389 5040885492754028492741771)
          ·
            refine ⟨7561328239131042739112657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040885492754028492741771 7561328239131042739112657)
            ·
              refine ⟨5670996179348282054334493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7561328239131042739112657 5670996179348282054334493)
              ·
                refine ⟨2126623567255605770375435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5670996179348282054334493 2126623567255605770375435)
                ·
                  refine ⟨3189935350883408655563153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126623567255605770375435 3189935350883408655563153)
                  ·
                    refine ⟨2392451513162556491672365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3189935350883408655563153 2392451513162556491672365)
                    ·
                      refine ⟨897169317435958684377137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392451513162556491672365 897169317435958684377137)
                      ·
                        rfl

theorem cell23_1747231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_1747231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747231 prefixEnd_1747231 := by exact prefixLift 1747231
  have htrace : WordTrace (prefixWord ++ tailWord_1747231) baseStart_1747231 baseEnd_1747231 := by
    simpa [prefixWord, tailWord_1747231, baseEnd_1747231] using wordTrace_append hprefix tailTrace_1747231
  have hstable : (prefixWord ++ tailWord_1747231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747231).length < 2 ^ (prefixWord ++ tailWord_1747231).sum := by decide
  have hdescent : baseEnd_1747231 < baseStart_1747231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747234 : List Nat := [3, 3, 1, 1, 3, 3, 9]
def baseStart_1747234 : Nat := 118140960795 + 1747234 * 2 ^ 59
def prefixEnd_1747234 : Nat := 4983230072969 + 3 ^ 40 * 1747234 * 2
def baseEnd_1747234 : Nat := 11076183430591631760983

theorem tailTrace_1747234 : CollatzResearch.WordTrace tailWord_1747234 prefixEnd_1747234 11076183430591631760983 := by
  unfold tailWord_1747234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931714838019274163792189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42484572901384731103445837 15931714838019274163792189)
  ·
    refine ⟨5974393064257227811422071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15931714838019274163792189 5974393064257227811422071)
    ·
      refine ⟨8961589596385841717133107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5974393064257227811422071 8961589596385841717133107)
      ·
        refine ⟨13442384394578762575699661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8961589596385841717133107 13442384394578762575699661)
        ·
          refine ⟨5040894147967035965887373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13442384394578762575699661 5040894147967035965887373)
          ·
            refine ⟨1890335305487638487207765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5040894147967035965887373 1890335305487638487207765)
            ·
              refine ⟨11076183430591631760983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1890335305487638487207765 11076183430591631760983)
              ·
                rfl

theorem cell23_1747234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 9].length) (baseStart_1747234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747234 prefixEnd_1747234 := by exact prefixLift 1747234
  have htrace : WordTrace (prefixWord ++ tailWord_1747234) baseStart_1747234 baseEnd_1747234 := by
    simpa [prefixWord, tailWord_1747234, baseEnd_1747234] using wordTrace_append hprefix tailTrace_1747234
  have hstable : (prefixWord ++ tailWord_1747234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747234).length < 2 ^ (prefixWord ++ tailWord_1747234).sum := by decide
  have hdescent : baseEnd_1747234 < baseStart_1747234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747239 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1747239 : Nat := 118140960795 + 1747239 * 2 ^ 59
def prefixEnd_1747239 : Nat := 4983230072969 + 3 ^ 40 * 1747239 * 2
def baseEnd_1747239 : Nat := 897173425281194653077101

theorem tailTrace_1747239 : CollatzResearch.WordTrace tailWord_1747239 prefixEnd_1747239 897173425281194653077101 := by
  unfold tailWord_1747239
  simp only [CollatzResearch.WordTrace]
  refine ⟨63727041717058982509100771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42484694478039321672733847 63727041717058982509100771)
  ·
    refine ⟨95590562575588473763651157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63727041717058982509100771 95590562575588473763651157)
    ·
      refine ⟨1120201905182677426917787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 95590562575588473763651157 1120201905182677426917787)
      ·
        refine ⟨1680302857774016140376681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120201905182677426917787 1680302857774016140376681)
        ·
          refine ⟨1260227143330512105282511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1680302857774016140376681 1260227143330512105282511)
          ·
            refine ⟨1890340714995768157923767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260227143330512105282511 1890340714995768157923767)
            ·
              refine ⟨2835511072493652236885651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890340714995768157923767 2835511072493652236885651)
              ·
                refine ⟨4253266608740478355328477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835511072493652236885651 4253266608740478355328477)
                ·
                  refine ⟨1594974978277679383248179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4253266608740478355328477 1594974978277679383248179)
                  ·
                    refine ⟨2392462467416519074872269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1594974978277679383248179 2392462467416519074872269)
                    ·
                      refine ⟨897173425281194653077101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392462467416519074872269 897173425281194653077101)
                      ·
                        rfl

theorem cell23_1747239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1747239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747239 prefixEnd_1747239 := by exact prefixLift 1747239
  have htrace : WordTrace (prefixWord ++ tailWord_1747239) baseStart_1747239 baseEnd_1747239 := by
    simpa [prefixWord, tailWord_1747239, baseEnd_1747239] using wordTrace_append hprefix tailTrace_1747239
  have hstable : (prefixWord ++ tailWord_1747239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747239).length < 2 ^ (prefixWord ++ tailWord_1747239).sum := by decide
  have hdescent : baseEnd_1747239 < baseStart_1747239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747265 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1747265 : Nat := 118140960795 + 1747265 * 2 ^ 59
def prefixEnd_1747265 : Nat := 4983230072969 + 3 ^ 40 * 1747265 * 2
def baseEnd_1747265 : Nat := 897186775778211551351981

theorem tailTrace_1747265 : CollatzResearch.WordTrace tailWord_1747265 prefixEnd_1747265 897186775778211551351981 := by
  unfold tailWord_1747265
  simp only [CollatzResearch.WordTrace]
  refine ⟨63727990014964788949547249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42485326676643192633031499 63727990014964788949547249)
  ·
    refine ⟨47795992511223591712160437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63727990014964788949547249 47795992511223591712160437)
    ·
      refine ⟨4480874297927211723015041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47795992511223591712160437 4480874297927211723015041)
      ·
        refine ⟨3360655723445408792261281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4480874297927211723015041 3360655723445408792261281)
        ·
          refine ⟨2520491792584056594195961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360655723445408792261281 2520491792584056594195961)
          ·
            refine ⟨1890368844438042445646971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2520491792584056594195961 1890368844438042445646971)
            ·
              refine ⟨2835553266657063668470457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890368844438042445646971 2835553266657063668470457)
              ·
                refine ⟨2126664949992797751352843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835553266657063668470457 2126664949992797751352843)
                ·
                  refine ⟨3189997424989196627029265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126664949992797751352843 3189997424989196627029265)
                  ·
                    refine ⟨2392498068741897470271949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3189997424989196627029265 2392498068741897470271949)
                    ·
                      refine ⟨897186775778211551351981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392498068741897470271949 897186775778211551351981)
                      ·
                        rfl

theorem cell23_1747265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1747265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747265 prefixEnd_1747265 := by exact prefixLift 1747265
  have htrace : WordTrace (prefixWord ++ tailWord_1747265) baseStart_1747265 baseEnd_1747265 := by
    simpa [prefixWord, tailWord_1747265, baseEnd_1747265] using wordTrace_append hprefix tailTrace_1747265
  have hstable : (prefixWord ++ tailWord_1747265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747265).length < 2 ^ (prefixWord ++ tailWord_1747265).sum := by decide
  have hdescent : baseEnd_1747265 < baseStart_1747265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747271 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_1747271 : Nat := 118140960795 + 1747271 * 2 ^ 59
def prefixEnd_1747271 : Nat := 4983230072969 + 3 ^ 40 * 1747271 * 2
def baseEnd_1747271 : Nat := 897189856662138527876953

theorem tailTrace_1747271 : CollatzResearch.WordTrace tailWord_1747271 prefixEnd_1747271 897189856662138527876953 := by
  unfold tailWord_1747271
  simp only [CollatzResearch.WordTrace]
  refine ⟨63728208852943051974265667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42485472568628701316177111 63728208852943051974265667)
  ·
    refine ⟨95592313279414577961398501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63728208852943051974265667 95592313279414577961398501)
    ·
      refine ⟨17923558739890233367762219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95592313279414577961398501 17923558739890233367762219)
      ·
        refine ⟨26885338109835350051643329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17923558739890233367762219 26885338109835350051643329)
        ·
          refine ⟨20164003582376512538732497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26885338109835350051643329 20164003582376512538732497)
          ·
            refine ⟨15123002686782384404049373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20164003582376512538732497 15123002686782384404049373)
            ·
              refine ⟨5671126007543394151518515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15123002686782384404049373 5671126007543394151518515)
              ·
                refine ⟨8506689011315091227277773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671126007543394151518515 8506689011315091227277773)
                ·
                  refine ⟨3190008379243159210229165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8506689011315091227277773 3190008379243159210229165)
                  ·
                    refine ⟨1196253142216184703835937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190008379243159210229165 1196253142216184703835937)
                    ·
                      refine ⟨897189856662138527876953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196253142216184703835937 897189856662138527876953)
                      ·
                        rfl

theorem cell23_1747271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_1747271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747271 prefixEnd_1747271 := by exact prefixLift 1747271
  have htrace : WordTrace (prefixWord ++ tailWord_1747271) baseStart_1747271 baseEnd_1747271 := by
    simpa [prefixWord, tailWord_1747271, baseEnd_1747271] using wordTrace_append hprefix tailTrace_1747271
  have hstable : (prefixWord ++ tailWord_1747271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747271).length < 2 ^ (prefixWord ++ tailWord_1747271).sum := by decide
  have hdescent : baseEnd_1747271 < baseStart_1747271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747297 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1747297 : Nat := 118140960795 + 1747297 * 2 ^ 59
def prefixEnd_1747297 : Nat := 4983230072969 + 3 ^ 40 * 1747297 * 2
def baseEnd_1747297 : Nat := 897203207159155426151833

theorem tailTrace_1747297 : CollatzResearch.WordTrace tailWord_1747297 prefixEnd_1747297 897203207159155426151833 := by
  unfold tailWord_1747297
  simp only [CollatzResearch.WordTrace]
  refine ⟨63729157150848858414712145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42486104767232572276474763 63729157150848858414712145)
  ·
    refine ⟨47796867863136643811034109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63729157150848858414712145 47796867863136643811034109)
    ·
      refine ⟨17923825448676241429137791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47796867863136643811034109 17923825448676241429137791)
      ·
        refine ⟨26885738173014362143706687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17923825448676241429137791 26885738173014362143706687)
        ·
          refine ⟨40328607259521543215560031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26885738173014362143706687 40328607259521543215560031)
          ·
            refine ⟨60492910889282314823340047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40328607259521543215560031 60492910889282314823340047)
            ·
              refine ⟨90739366333923472235010071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60492910889282314823340047 90739366333923472235010071)
              ·
                refine ⟨136109049500885208352515107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90739366333923472235010071 136109049500885208352515107)
                ·
                  refine ⟨204163574251327812528772661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136109049500885208352515107 204163574251327812528772661)
                  ·
                    refine ⟨19140335086061982424572437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 204163574251327812528772661 19140335086061982424572437)
                    ·
                      refine ⟨897203207159155426151833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19140335086061982424572437 897203207159155426151833)
                      ·
                        rfl

theorem cell23_1747297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1747297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747297 prefixEnd_1747297 := by exact prefixLift 1747297
  have htrace : WordTrace (prefixWord ++ tailWord_1747297) baseStart_1747297 baseEnd_1747297 := by
    simpa [prefixWord, tailWord_1747297, baseEnd_1747297] using wordTrace_append hprefix tailTrace_1747297
  have hstable : (prefixWord ++ tailWord_1747297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747297).length < 2 ^ (prefixWord ++ tailWord_1747297).sum := by decide
  have hdescent : baseEnd_1747297 < baseStart_1747297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747314 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1747314 : Nat := 118140960795 + 1747314 * 2 ^ 59
def prefixEnd_1747314 : Nat := 4983230072969 + 3 ^ 40 * 1747314 * 2
def baseEnd_1747314 : Nat := 897211936330281859639255

theorem tailTrace_1747314 : CollatzResearch.WordTrace tailWord_1747314 prefixEnd_1747314 897211936330281859639255 := by
  unfold tailWord_1747314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15932444297946817579520249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42486518127858180212053997 15932444297946817579520249)
  ·
    refine ⟨11949333223460113184640187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15932444297946817579520249 11949333223460113184640187)
    ·
      refine ⟨17923999835190169776960281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11949333223460113184640187 17923999835190169776960281)
      ·
        refine ⟨13442999876392627332720211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17923999835190169776960281 13442999876392627332720211)
        ·
          refine ⟨20164499814588940999080317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13442999876392627332720211 20164499814588940999080317)
          ·
            refine ⟨7561687430470852874655119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20164499814588940999080317 7561687430470852874655119)
            ·
              refine ⟨11342531145706279311982679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7561687430470852874655119 11342531145706279311982679)
              ·
                refine ⟨17013796718559418967974019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11342531145706279311982679 17013796718559418967974019)
                ·
                  refine ⟨25520695077839128451961029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17013796718559418967974019 25520695077839128451961029)
                  ·
                    refine ⟨4785130327094836584742693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25520695077839128451961029 4785130327094836584742693)
                    ·
                      refine ⟨897211936330281859639255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4785130327094836584742693 897211936330281859639255)
                      ·
                        rfl

theorem cell23_1747314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1747314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747314 prefixEnd_1747314 := by exact prefixLift 1747314
  have htrace : WordTrace (prefixWord ++ tailWord_1747314) baseStart_1747314 baseEnd_1747314 := by
    simpa [prefixWord, tailWord_1747314, baseEnd_1747314] using wordTrace_append hprefix tailTrace_1747314
  have hstable : (prefixWord ++ tailWord_1747314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747314).length < 2 ^ (prefixWord ++ tailWord_1747314).sum := by decide
  have hdescent : baseEnd_1747314 < baseStart_1747314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747327 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_1747327 : Nat := 118140960795 + 1747327 * 2 ^ 59
def prefixEnd_1747327 : Nat := 4983230072969 + 3 ^ 40 * 1747327 * 2
def baseEnd_1747327 : Nat := 897218611578790308776695

theorem tailTrace_1747327 : CollatzResearch.WordTrace tailWord_1747327 prefixEnd_1747327 897218611578790308776695 := by
  unfold tailWord_1747327
  simp only [CollatzResearch.WordTrace]
  refine ⟨63730251340740173538304235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42486834227160115692202823 63730251340740173538304235)
  ·
    refine ⟨95595377011110260307456353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63730251340740173538304235 95595377011110260307456353)
    ·
      refine ⟨71696532758332695230592265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95595377011110260307456353 71696532758332695230592265)
      ·
        refine ⟨53772399568749521422944199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71696532758332695230592265 53772399568749521422944199)
        ·
          refine ⟨80658599353124282134416299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53772399568749521422944199 80658599353124282134416299)
          ·
            refine ⟨120987899029686423201624449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80658599353124282134416299 120987899029686423201624449)
            ·
              refine ⟨90740924272264817401218337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120987899029686423201624449 90740924272264817401218337)
              ·
                refine ⟨68055693204198613050913753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90740924272264817401218337 68055693204198613050913753)
                ·
                  refine ⟨51041769903148959788185315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68055693204198613050913753 51041769903148959788185315)
                  ·
                    refine ⟨76562654854723439682277973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51041769903148959788185315 76562654854723439682277973)
                    ·
                      refine ⟨897218611578790308776695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 76562654854723439682277973 897218611578790308776695)
                      ·
                        rfl

theorem cell23_1747327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_1747327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747327 prefixEnd_1747327 := by exact prefixLift 1747327
  have htrace : WordTrace (prefixWord ++ tailWord_1747327) baseStart_1747327 baseEnd_1747327 := by
    simpa [prefixWord, tailWord_1747327, baseEnd_1747327] using wordTrace_append hprefix tailTrace_1747327
  have hstable : (prefixWord ++ tailWord_1747327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747327).length < 2 ^ (prefixWord ++ tailWord_1747327).sum := by decide
  have hdescent : baseEnd_1747327 < baseStart_1747327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747352 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1747352 : Nat := 118140960795 + 1747352 * 2 ^ 59
def prefixEnd_1747352 : Nat := 4983230072969 + 3 ^ 40 * 1747352 * 2
def baseEnd_1747352 : Nat := 897231448595152710964081

theorem tailTrace_1747352 : CollatzResearch.WordTrace tailWord_1747352 prefixEnd_1747352 897231448595152710964081 := by
  unfold tailWord_1747352
  simp only [CollatzResearch.WordTrace]
  refine ⟨31865581582824801403982155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42487442110433068538642873 31865581582824801403982155)
  ·
    refine ⟨47798372374237202105973233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31865581582824801403982155 47798372374237202105973233)
    ·
      refine ⟨35848779280677901579479925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47798372374237202105973233 35848779280677901579479925)
      ·
        refine ⟨3360823057563553273076243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35848779280677901579479925 3360823057563553273076243)
        ·
          refine ⟨5041234586345329909614365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360823057563553273076243 5041234586345329909614365)
          ·
            refine ⟨1890462969879498716105387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5041234586345329909614365 1890462969879498716105387)
            ·
              refine ⟨2835694454819248074158081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890462969879498716105387 2835694454819248074158081)
              ·
                refine ⟨2126770841114436055618561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835694454819248074158081 2126770841114436055618561)
                ·
                  refine ⟨1595078130835827041713921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2126770841114436055618561 1595078130835827041713921)
                  ·
                    refine ⟨1196308598126870281285441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1595078130835827041713921 1196308598126870281285441)
                    ·
                      refine ⟨897231448595152710964081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196308598126870281285441 897231448595152710964081)
                      ·
                        rfl

theorem cell23_1747352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1747352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747352 prefixEnd_1747352 := by exact prefixLift 1747352
  have htrace : WordTrace (prefixWord ++ tailWord_1747352) baseStart_1747352 baseEnd_1747352 := by
    simpa [prefixWord, tailWord_1747352, baseEnd_1747352] using wordTrace_append hprefix tailTrace_1747352
  have hstable : (prefixWord ++ tailWord_1747352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747352).length < 2 ^ (prefixWord ++ tailWord_1747352).sum := by decide
  have hdescent : baseEnd_1747352 < baseStart_1747352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747358 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1747358 : Nat := 118140960795 + 1747358 * 2 ^ 59
def prefixEnd_1747358 : Nat := 4983230072969 + 3 ^ 40 * 1747358 * 2
def baseEnd_1747358 : Nat := 99692725497675520832117

theorem tailTrace_1747358 : CollatzResearch.WordTrace tailWord_1747358 prefixEnd_1747358 99692725497675520832117 := by
  unfold tailWord_1747358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966422750453483229085341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42487588002418577221788485 7966422750453483229085341)
  ·
    refine ⟨2987408531420056210907003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7966422750453483229085341 2987408531420056210907003)
    ·
      refine ⟨4481112797130084316360505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987408531420056210907003 4481112797130084316360505)
      ·
        refine ⟨3360834597847563237270379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4481112797130084316360505 3360834597847563237270379)
        ·
          refine ⟨5041251896771344855905569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360834597847563237270379 5041251896771344855905569)
          ·
            refine ⟨3780938922578508641929177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5041251896771344855905569 3780938922578508641929177)
            ·
              refine ⟨2835704191933881481446883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780938922578508641929177 2835704191933881481446883)
              ·
                refine ⟨4253556287900822222170325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835704191933881481446883 4253556287900822222170325)
                ·
                  refine ⟨99692725497675520832117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4253556287900822222170325 99692725497675520832117)
                  ·
                    rfl

theorem cell23_1747358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1747358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747358 prefixEnd_1747358 := by exact prefixLift 1747358
  have htrace : WordTrace (prefixWord ++ tailWord_1747358) baseStart_1747358 baseEnd_1747358 := by
    simpa [prefixWord, tailWord_1747358, baseEnd_1747358] using wordTrace_append hprefix tailTrace_1747358
  have hstable : (prefixWord ++ tailWord_1747358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747358).length < 2 ^ (prefixWord ++ tailWord_1747358).sum := by decide
  have hdescent : baseEnd_1747358 < baseStart_1747358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747364 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1747364 : Nat := 118140960795 + 1747364 * 2 ^ 59
def prefixEnd_1747364 : Nat := 4983230072969 + 3 ^ 40 * 1747364 * 2
def baseEnd_1747364 : Nat := 897237610363006664014025

theorem tailTrace_1747364 : CollatzResearch.WordTrace tailWord_1747364 prefixEnd_1747364 897237610363006664014025 := by
  unfold tailWord_1747364
  simp only [CollatzResearch.WordTrace]
  refine ⟨31865800420803064428700573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42487733894404085904934097 31865800420803064428700573)
  ·
    refine ⟨11949675157801149160762715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31865800420803064428700573 11949675157801149160762715)
    ·
      refine ⟨17924512736701723741144073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11949675157801149160762715 17924512736701723741144073)
      ·
        refine ⟨13443384552526292805858055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17924512736701723741144073 13443384552526292805858055)
        ·
          refine ⟨20165076828789439208787083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13443384552526292805858055 20165076828789439208787083)
          ·
            refine ⟨30247615243184158813180625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20165076828789439208787083 30247615243184158813180625)
            ·
              refine ⟨22685711432388119109885469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30247615243184158813180625 22685711432388119109885469)
              ·
                refine ⟨8507141787145544666207051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22685711432388119109885469 8507141787145544666207051)
                ·
                  refine ⟨12760712680718316999310577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8507141787145544666207051 12760712680718316999310577)
                  ·
                    refine ⟨9570534510538737749482933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12760712680718316999310577 9570534510538737749482933)
                    ·
                      refine ⟨897237610363006664014025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9570534510538737749482933 897237610363006664014025)
                      ·
                        rfl

theorem cell23_1747364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1747364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747364 prefixEnd_1747364 := by exact prefixLift 1747364
  have htrace : WordTrace (prefixWord ++ tailWord_1747364) baseStart_1747364 baseEnd_1747364 := by
    simpa [prefixWord, tailWord_1747364, baseEnd_1747364] using wordTrace_append hprefix tailTrace_1747364
  have hstable : (prefixWord ++ tailWord_1747364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747364).length < 2 ^ (prefixWord ++ tailWord_1747364).sum := by decide
  have hdescent : baseEnd_1747364 < baseStart_1747364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747368 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1747368 : Nat := 118140960795 + 1747368 * 2 ^ 59
def prefixEnd_1747368 : Nat := 4983230072969 + 3 ^ 40 * 1747368 * 2
def baseEnd_1747368 : Nat := 897239664285624648364007

theorem tailTrace_1747368 : CollatzResearch.WordTrace tailWord_1747368 prefixEnd_1747368 897239664285624648364007 := by
  unfold tailWord_1747368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31865873366795818770273379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42487831155727758360364505 31865873366795818770273379)
  ·
    refine ⟨47798810050193728155410069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31865873366795818770273379 47798810050193728155410069)
    ·
      refine ⟨2240569221102831007284847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47798810050193728155410069 2240569221102831007284847)
      ·
        refine ⟨3360853831654246510927271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240569221102831007284847 3360853831654246510927271)
        ·
          refine ⟨5041280747481369766390907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360853831654246510927271 5041280747481369766390907)
          ·
            refine ⟨7561921121222054649586361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5041280747481369766390907 7561921121222054649586361)
            ·
              refine ⟨5671440840916540987189771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7561921121222054649586361 5671440840916540987189771)
              ·
                refine ⟨8507161261374811480784657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671440840916540987189771 8507161261374811480784657)
                ·
                  refine ⟨6380370946031108610588493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8507161261374811480784657 6380370946031108610588493)
                  ·
                    refine ⟨2392639104761665728970685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6380370946031108610588493 2392639104761665728970685)
                    ·
                      refine ⟨897239664285624648364007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392639104761665728970685 897239664285624648364007)
                      ·
                        rfl

theorem cell23_1747368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1747368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747368 prefixEnd_1747368 := by exact prefixLift 1747368
  have htrace : WordTrace (prefixWord ++ tailWord_1747368) baseStart_1747368 baseEnd_1747368 := by
    simpa [prefixWord, tailWord_1747368, baseEnd_1747368] using wordTrace_append hprefix tailTrace_1747368
  have hstable : (prefixWord ++ tailWord_1747368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747368).length < 2 ^ (prefixWord ++ tailWord_1747368).sum := by decide
  have hdescent : baseEnd_1747368 < baseStart_1747368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747431 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 6]
def baseStart_1747431 : Nat := 118140960795 + 1747431 * 2 ^ 59
def prefixEnd_1747431 : Nat := 4983230072969 + 3 ^ 40 * 1747431 * 2
def baseEnd_1747431 : Nat := 99696890396317544652913

theorem tailTrace_1747431 : CollatzResearch.WordTrace tailWord_1747431 prefixEnd_1747431 99696890396317544652913 := by
  unfold tailWord_1747431
  simp only [CollatzResearch.WordTrace]
  refine ⟨63734044532363399300090147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42489363021575599533393431 63734044532363399300090147)
  ·
    refine ⟨95601066798545098950135221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63734044532363399300090147 95601066798545098950135221)
    ·
      refine ⟨8962600012363603026575177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95601066798545098950135221 8962600012363603026575177)
      ·
        refine ⟨6721950009272702269931383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8962600012363603026575177 6721950009272702269931383)
        ·
          refine ⟨10082925013909053404897075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721950009272702269931383 10082925013909053404897075)
          ·
            refine ⟨15124387520863580107345613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10082925013909053404897075 15124387520863580107345613)
            ·
              refine ⟨5671645320323842540254605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15124387520863580107345613 5671645320323842540254605)
              ·
                refine ⟨2126866995121440952595477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5671645320323842540254605 2126866995121440952595477)
                ·
                  refine ⟨99696890396317544652913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2126866995121440952595477 99696890396317544652913)
                  ·
                    rfl

theorem cell23_1747431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 6].length) (baseStart_1747431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747431 prefixEnd_1747431 := by exact prefixLift 1747431
  have htrace : WordTrace (prefixWord ++ tailWord_1747431) baseStart_1747431 baseEnd_1747431 := by
    simpa [prefixWord, tailWord_1747431, baseEnd_1747431] using wordTrace_append hprefix tailTrace_1747431
  have hstable : (prefixWord ++ tailWord_1747431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747431).length < 2 ^ (prefixWord ++ tailWord_1747431).sum := by decide
  have hdescent : baseEnd_1747431 < baseStart_1747431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747461 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_1747461 : Nat := 118140960795 + 1747461 * 2 ^ 59
def prefixEnd_1747461 : Nat := 4983230072969 + 3 ^ 40 * 1747461 * 2
def baseEnd_1747461 : Nat := 299095805995497594833693

theorem tailTrace_1747461 : CollatzResearch.WordTrace tailWord_1747461 prefixEnd_1747461 299095805995497594833693 := by
  unfold tailWord_1747461
  simp only [CollatzResearch.WordTrace]
  refine ⟨63735138722254714423682237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42490092481503142949121491 63735138722254714423682237)
  ·
    refine ⟨23900677020845517908880839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63735138722254714423682237 23900677020845517908880839)
    ·
      refine ⟨35851015531268276863321259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23900677020845517908880839 35851015531268276863321259)
      ·
        refine ⟨53776523296902415294981889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35851015531268276863321259 53776523296902415294981889)
        ·
          refine ⟨40332392472676811471236417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53776523296902415294981889 40332392472676811471236417)
          ·
            refine ⟨30249294354507608603427313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40332392472676811471236417 30249294354507608603427313)
            ·
              refine ⟨22686970765880706452570485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30249294354507608603427313 22686970765880706452570485)
              ·
                refine ⟨2126903509301316229928483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22686970765880706452570485 2126903509301316229928483)
                ·
                  refine ⟨3190355263951974344892725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126903509301316229928483 3190355263951974344892725)
                  ·
                    refine ⟨299095805995497594833693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3190355263951974344892725 299095805995497594833693)
                    ·
                      rfl

theorem cell23_1747461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_1747461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747461 prefixEnd_1747461 := by exact prefixLift 1747461
  have htrace : WordTrace (prefixWord ++ tailWord_1747461) baseStart_1747461 baseEnd_1747461 := by
    simpa [prefixWord, tailWord_1747461, baseEnd_1747461] using wordTrace_append hprefix tailTrace_1747461
  have hstable : (prefixWord ++ tailWord_1747461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747461).length < 2 ^ (prefixWord ++ tailWord_1747461).sum := by decide
  have hdescent : baseEnd_1747461 < baseStart_1747461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747469 : List Nat := [1, 7, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1747469 : Nat := 118140960795 + 1747469 * 2 ^ 59
def prefixEnd_1747469 : Nat := 4983230072969 + 3 ^ 40 * 1747469 * 2
def baseEnd_1747469 : Nat := 299097175277242917733681

theorem tailTrace_1747469 : CollatzResearch.WordTrace tailWord_1747469 prefixEnd_1747469 299097175277242917733681 := by
  unfold tailWord_1747469
  simp only [CollatzResearch.WordTrace]
  refine ⟨63735430506225731789973461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42490287004150487859982307 63735430506225731789973461)
  ·
    refine ⟨1493799152489665588827503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 63735430506225731789973461 1493799152489665588827503)
    ·
      refine ⟨2240698728734498383241255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493799152489665588827503 2240698728734498383241255)
      ·
        refine ⟨3361048093101747574861883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240698728734498383241255 3361048093101747574861883)
        ·
          refine ⟨5041572139652621362292825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361048093101747574861883 5041572139652621362292825)
          ·
            refine ⟨3781179104739466021719619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5041572139652621362292825 3781179104739466021719619)
            ·
              refine ⟨5671768657109199032579429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781179104739466021719619 5671768657109199032579429)
              ·
                refine ⟨1063456623207974818608643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5671768657109199032579429 1063456623207974818608643)
                ·
                  refine ⟨1595184934811962227912965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063456623207974818608643 1595184934811962227912965)
                  ·
                    refine ⟨299097175277242917733681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595184934811962227912965 299097175277242917733681)
                    ·
                      rfl

theorem cell23_1747469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1747469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747469 prefixEnd_1747469 := by exact prefixLift 1747469
  have htrace : WordTrace (prefixWord ++ tailWord_1747469) baseStart_1747469 baseEnd_1747469 := by
    simpa [prefixWord, tailWord_1747469, baseEnd_1747469] using wordTrace_append hprefix tailTrace_1747469
  have hstable : (prefixWord ++ tailWord_1747469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747469).length < 2 ^ (prefixWord ++ tailWord_1747469).sum := by decide
  have hdescent : baseEnd_1747469 < baseStart_1747469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747475 : List Nat := [1, 1, 1, 2, 1, 5, 3, 4, 1, 1, 3]
def baseStart_1747475 : Nat := 118140960795 + 1747475 * 2 ^ 59
def prefixEnd_1747475 : Nat := 4983230072969 + 3 ^ 40 * 1747475 * 2
def baseEnd_1747475 : Nat := 897294606715655729726015

theorem tailTrace_1747475 : CollatzResearch.WordTrace tailWord_1747475 prefixEnd_1747475 897294606715655729726015 := by
  unfold tailWord_1747475
  simp only [CollatzResearch.WordTrace]
  refine ⟨63735649344203994814691879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42490432896135996543127919 63735649344203994814691879)
  ·
    refine ⟨95603474016305992222037819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63735649344203994814691879 95603474016305992222037819)
    ·
      refine ⟨143405211024458988333056729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95603474016305992222037819 143405211024458988333056729)
      ·
        refine ⟨107553908268344241249792547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143405211024458988333056729 107553908268344241249792547)
        ·
          refine ⟨161330862402516361874688821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107553908268344241249792547 161330862402516361874688821)
          ·
            refine ⟨15124768350235908925752077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161330862402516361874688821 15124768350235908925752077)
            ·
              refine ⟨5671788131338465847157029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15124768350235908925752077 5671788131338465847157029)
              ·
                refine ⟨1063460274625962346341943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5671788131338465847157029 1063460274625962346341943)
                ·
                  refine ⟨1595190411938943519512915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063460274625962346341943 1595190411938943519512915)
                  ·
                    refine ⟨2392785617908415279269373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1595190411938943519512915 2392785617908415279269373)
                    ·
                      refine ⟨897294606715655729726015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392785617908415279269373 897294606715655729726015)
                      ·
                        rfl

theorem cell23_1747475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 1, 3].length) (baseStart_1747475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747475 prefixEnd_1747475 := by exact prefixLift 1747475
  have htrace : WordTrace (prefixWord ++ tailWord_1747475) baseStart_1747475 baseEnd_1747475 := by
    simpa [prefixWord, tailWord_1747475, baseEnd_1747475] using wordTrace_append hprefix tailTrace_1747475
  have hstable : (prefixWord ++ tailWord_1747475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747475).length < 2 ^ (prefixWord ++ tailWord_1747475).sum := by decide
  have hdescent : baseEnd_1747475 < baseStart_1747475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747491 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 1, 6]
def baseStart_1747491 : Nat := 118140960795 + 1747491 * 2 ^ 59
def prefixEnd_1747491 : Nat := 4983230072969 + 3 ^ 40 * 1747491 * 2
def baseEnd_1747491 : Nat := 299100940802042555708647

theorem tailTrace_1747491 : CollatzResearch.WordTrace tailWord_1747491 prefixEnd_1747491 299100940802042555708647 := by
  unfold tailWord_1747491
  simp only [CollatzResearch.WordTrace]
  refine ⟨63736232912146029547274327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42490821941430686364849551 63736232912146029547274327)
  ·
    refine ⟨95604349368219044320911491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63736232912146029547274327 95604349368219044320911491)
    ·
      refine ⟨143406524052328566481367237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95604349368219044320911491 143406524052328566481367237)
      ·
        refine ⟨26888723259811606215256357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143406524052328566481367237 26888723259811606215256357)
        ·
          refine ⟨5041635611214676165360567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26888723259811606215256357 5041635611214676165360567)
          ·
            refine ⟨7562453416822014248040851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5041635611214676165360567 7562453416822014248040851)
            ·
              refine ⟨11343680125233021372061277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562453416822014248040851 11343680125233021372061277)
              ·
                refine ⟨4253880046962383014522979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11343680125233021372061277 4253880046962383014522979)
                ·
                  refine ⟨6380820070443574521784469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253880046962383014522979 6380820070443574521784469)
                  ·
                    refine ⟨299100940802042555708647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6380820070443574521784469 299100940802042555708647)
                    ·
                      rfl

theorem cell23_1747491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 6].length) (baseStart_1747491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747491 prefixEnd_1747491 := by exact prefixLift 1747491
  have htrace : WordTrace (prefixWord ++ tailWord_1747491) baseStart_1747491 baseEnd_1747491 := by
    simpa [prefixWord, tailWord_1747491, baseEnd_1747491] using wordTrace_append hprefix tailTrace_1747491
  have hstable : (prefixWord ++ tailWord_1747491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747491).length < 2 ^ (prefixWord ++ tailWord_1747491).sum := by decide
  have hdescent : baseEnd_1747491 < baseStart_1747491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747492 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1747492 : Nat := 118140960795 + 1747492 * 2 ^ 59
def prefixEnd_1747492 : Nat := 4983230072969 + 3 ^ 40 * 1747492 * 2
def baseEnd_1747492 : Nat := 897303335886782163213437

theorem tailTrace_1747492 : CollatzResearch.WordTrace tailWord_1747492 prefixEnd_1747492 897303335886782163213437 := by
  unfold tailWord_1747492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31868134692571203359030365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42490846256761604478707153 31868134692571203359030365)
  ·
    refine ⟨11950550509714201259636387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31868134692571203359030365 11950550509714201259636387)
    ·
      refine ⟨17925825764571301889454581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11950550509714201259636387 17925825764571301889454581)
      ·
        refine ⟨1680546165428559552136367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17925825764571301889454581 1680546165428559552136367)
        ·
          refine ⟨2520819248142839328204551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680546165428559552136367 2520819248142839328204551)
          ·
            refine ⟨3781228872214258992306827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520819248142839328204551 3781228872214258992306827)
            ·
              refine ⟨5671843308321388488460241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781228872214258992306827 5671843308321388488460241)
              ·
                refine ⟨4253882481241041366345181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5671843308321388488460241 4253882481241041366345181)
                ·
                  refine ⟨1595205930465390512379443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4253882481241041366345181 1595205930465390512379443)
                  ·
                    refine ⟨2392808895698085768569165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1595205930465390512379443 2392808895698085768569165)
                    ·
                      refine ⟨897303335886782163213437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392808895698085768569165 897303335886782163213437)
                      ·
                        rfl

theorem cell23_1747492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1747492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747492 prefixEnd_1747492 := by exact prefixLift 1747492
  have htrace : WordTrace (prefixWord ++ tailWord_1747492) baseStart_1747492 baseEnd_1747492 := by
    simpa [prefixWord, tailWord_1747492, baseEnd_1747492] using wordTrace_append hprefix tailTrace_1747492
  have hstable : (prefixWord ++ tailWord_1747492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747492).length < 2 ^ (prefixWord ++ tailWord_1747492).sum := by decide
  have hdescent : baseEnd_1747492 < baseStart_1747492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747498 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1747498 : Nat := 118140960795 + 1747498 * 2 ^ 59
def prefixEnd_1747498 : Nat := 4983230072969 + 3 ^ 40 * 1747498 * 2
def baseEnd_1747498 : Nat := 897306416770709139738409

theorem tailTrace_1747498 : CollatzResearch.WordTrace tailWord_1747498 prefixEnd_1747498 897306416770709139738409 := by
  unfold tailWord_1747498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934122055780167435694787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42490992148747113161852765 15934122055780167435694787)
  ·
    refine ⟨23901183083670251153542181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15934122055780167435694787 23901183083670251153542181)
    ·
      refine ⟨4481471828188172091289159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23901183083670251153542181 4481471828188172091289159)
      ·
        refine ⟨6722207742282258136933739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481471828188172091289159 6722207742282258136933739)
        ·
          refine ⟨10083311613423387205400609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722207742282258136933739 10083311613423387205400609)
          ·
            refine ⟨7562483710067540404050457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10083311613423387205400609 7562483710067540404050457)
            ·
              refine ⟨5671862782550655303037843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7562483710067540404050457 5671862782550655303037843)
              ·
                refine ⟨8507794173825982954556765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671862782550655303037843 8507794173825982954556765)
                ·
                  refine ⟨3190422815184743607958787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8507794173825982954556765 3190422815184743607958787)
                  ·
                    refine ⟨4785634222777115411938181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3190422815184743607958787 4785634222777115411938181)
                    ·
                      refine ⟨897306416770709139738409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4785634222777115411938181 897306416770709139738409)
                      ·
                        rfl

theorem cell23_1747498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1747498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747498 prefixEnd_1747498 := by exact prefixLift 1747498
  have htrace : WordTrace (prefixWord ++ tailWord_1747498) baseStart_1747498 baseEnd_1747498 := by
    simpa [prefixWord, tailWord_1747498, baseEnd_1747498] using wordTrace_append hprefix tailTrace_1747498
  have hstable : (prefixWord ++ tailWord_1747498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747498).length < 2 ^ (prefixWord ++ tailWord_1747498).sum := by decide
  have hdescent : baseEnd_1747498 < baseStart_1747498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747504 : List Nat := [2, 1, 1, 1, 2, 3, 2, 11]
def baseStart_1747504 : Nat := 118140960795 + 1747504 * 2 ^ 59
def prefixEnd_1747504 : Nat := 4983230072969 + 3 ^ 40 * 1747504 * 2
def baseEnd_1747504 : Nat := 33233685098319856157903

theorem tailTrace_1747504 : CollatzResearch.WordTrace tailWord_1747504 prefixEnd_1747504 33233685098319856157903 := by
  unfold tailWord_1747504
  simp only [CollatzResearch.WordTrace]
  refine ⟨31868353530549466383748783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42491138040732621844998377 31868353530549466383748783)
  ·
    refine ⟨47802530295824199575623175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31868353530549466383748783 47802530295824199575623175)
    ·
      refine ⟨71703795443736299363434763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47802530295824199575623175 71703795443736299363434763)
      ·
        refine ⟨107555693165604449045152145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71703795443736299363434763 107555693165604449045152145)
        ·
          refine ⟨80666769874203336783864109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107555693165604449045152145 80666769874203336783864109)
          ·
            refine ⟨30250038702826251293949041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80666769874203336783864109 30250038702826251293949041)
            ·
              refine ⟨22687529027119688470461781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30250038702826251293949041 22687529027119688470461781)
              ·
                refine ⟨33233685098319856157903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22687529027119688470461781 33233685098319856157903)
                ·
                  rfl

theorem cell23_1747504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 11].length) (baseStart_1747504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747504 prefixEnd_1747504 := by exact prefixLift 1747504
  have htrace : WordTrace (prefixWord ++ tailWord_1747504) baseStart_1747504 baseEnd_1747504 := by
    simpa [prefixWord, tailWord_1747504, baseEnd_1747504] using wordTrace_append hprefix tailTrace_1747504
  have hstable : (prefixWord ++ tailWord_1747504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747504).length < 2 ^ (prefixWord ++ tailWord_1747504).sum := by decide
  have hdescent : baseEnd_1747504 < baseStart_1747504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747511 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_1747511 : Nat := 118140960795 + 1747511 * 2 ^ 59
def prefixEnd_1747511 : Nat := 4983230072969 + 3 ^ 40 * 1747511 * 2
def baseEnd_1747511 : Nat := 897313092019217588875849

theorem tailTrace_1747511 : CollatzResearch.WordTrace tailWord_1747511 prefixEnd_1747511 897313092019217588875849 := by
  unfold tailWord_1747511
  simp only [CollatzResearch.WordTrace]
  refine ⟨63736962372073572963002387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42491308248049048642001591 63736962372073572963002387)
  ·
    refine ⟨95605443558110359444503581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63736962372073572963002387 95605443558110359444503581)
    ·
      refine ⟨35852041334291384791688843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95605443558110359444503581 35852041334291384791688843)
      ·
        refine ⟨53778062001437077187533265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35852041334291384791688843 53778062001437077187533265)
        ·
          refine ⟨40333546501077807890649949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53778062001437077187533265 40333546501077807890649949)
          ·
            refine ⟨15125079937904177958993731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40333546501077807890649949 15125079937904177958993731)
            ·
              refine ⟨22687619906856266938490597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15125079937904177958993731 22687619906856266938490597)
              ·
                refine ⟨4253928732535550050966987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22687619906856266938490597 4253928732535550050966987)
                ·
                  refine ⟨6380893098803325076450481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253928732535550050966987 6380893098803325076450481)
                  ·
                    refine ⟨4785669824102493807337861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6380893098803325076450481 4785669824102493807337861)
                    ·
                      refine ⟨897313092019217588875849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4785669824102493807337861 897313092019217588875849)
                      ·
                        rfl

theorem cell23_1747511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_1747511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747511 prefixEnd_1747511 := by exact prefixLift 1747511
  have htrace : WordTrace (prefixWord ++ tailWord_1747511) baseStart_1747511 baseEnd_1747511 := by
    simpa [prefixWord, tailWord_1747511, baseEnd_1747511] using wordTrace_append hprefix tailTrace_1747511
  have hstable : (prefixWord ++ tailWord_1747511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747511).length < 2 ^ (prefixWord ++ tailWord_1747511).sum := by decide
  have hdescent : baseEnd_1747511 < baseStart_1747511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747521 : List Nat := [1, 2, 5, 1, 1, 3, 10]
def baseStart_1747521 : Nat := 118140960795 + 1747521 * 2 ^ 59
def prefixEnd_1747521 : Nat := 4983230072969 + 3 ^ 40 * 1747521 * 2
def baseEnd_1747521 : Nat := 11078002800318056169763

theorem tailTrace_1747521 : CollatzResearch.WordTrace tailWord_1747521 prefixEnd_1747521 11078002800318056169763 := by
  unfold tailWord_1747521
  simp only [CollatzResearch.WordTrace]
  refine ⟨63737327102037344670866417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42491551401358229780577611 63737327102037344670866417)
  ·
    refine ⟨47802995326528008503149813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63737327102037344670866417 47802995326528008503149813)
    ·
      refine ⟨4481530811862000797170295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47802995326528008503149813 4481530811862000797170295)
      ·
        refine ⟨6722296217793001195755443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481530811862000797170295 6722296217793001195755443)
        ·
          refine ⟨10083444326689501793633165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722296217793001195755443 10083444326689501793633165)
          ·
            refine ⟨3781291622508563172612437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10083444326689501793633165 3781291622508563172612437)
            ·
              refine ⟨11078002800318056169763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3781291622508563172612437 11078002800318056169763)
              ·
                rfl

theorem cell23_1747521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 10].length) (baseStart_1747521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747521 prefixEnd_1747521 := by exact prefixLift 1747521
  have htrace : WordTrace (prefixWord ++ tailWord_1747521) baseStart_1747521 baseEnd_1747521 := by
    simpa [prefixWord, tailWord_1747521, baseEnd_1747521] using wordTrace_append hprefix tailTrace_1747521
  have hstable : (prefixWord ++ tailWord_1747521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747521).length < 2 ^ (prefixWord ++ tailWord_1747521).sum := by decide
  have hdescent : baseEnd_1747521 < baseStart_1747521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747525 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_1747525 : Nat := 118140960795 + 1747525 * 2 ^ 59
def prefixEnd_1747525 : Nat := 4983230072969 + 3 ^ 40 * 1747525 * 2
def baseEnd_1747525 : Nat := 299106760249460178033595

theorem tailTrace_1747525 : CollatzResearch.WordTrace tailWord_1747525 prefixEnd_1747525 299106760249460178033595 := by
  unfold tailWord_1747525
  simp only [CollatzResearch.WordTrace]
  refine ⟨63737472994022853354012029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42491648662681902236008019 63737472994022853354012029)
  ·
    refine ⟨23901552372758570007754511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63737472994022853354012029 23901552372758570007754511)
    ·
      refine ⟨35852328559137855011631767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23901552372758570007754511 35852328559137855011631767)
      ·
        refine ⟨53778492838706782517447651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35852328559137855011631767 53778492838706782517447651)
        ·
          refine ⟨80667739258060173776171477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53778492838706782517447651 80667739258060173776171477)
          ·
            refine ⟨1890650138860785322879019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 80667739258060173776171477 1890650138860785322879019)
            ·
              refine ⟨2835975208291177984318529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890650138860785322879019 2835975208291177984318529)
              ·
                refine ⟨2126981406218383488238897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835975208291177984318529 2126981406218383488238897)
                ·
                  refine ⟨1595236054663787616179173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2126981406218383488238897 1595236054663787616179173)
                  ·
                    refine ⟨299106760249460178033595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595236054663787616179173 299106760249460178033595)
                    ·
                      rfl

theorem cell23_1747525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_1747525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747525 prefixEnd_1747525 := by exact prefixLift 1747525
  have htrace : WordTrace (prefixWord ++ tailWord_1747525) baseStart_1747525 baseEnd_1747525 := by
    simpa [prefixWord, tailWord_1747525, baseEnd_1747525] using wordTrace_append hprefix tailTrace_1747525
  have hstable : (prefixWord ++ tailWord_1747525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747525).length < 2 ^ (prefixWord ++ tailWord_1747525).sum := by decide
  have hdescent : baseEnd_1747525 < baseStart_1747525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747531 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 3]
def baseStart_1747531 : Nat := 118140960795 + 1747531 * 2 ^ 59
def prefixEnd_1747531 : Nat := 4983230072969 + 3 ^ 40 * 1747531 * 2
def baseEnd_1747531 : Nat := 897323361632307510625757

theorem tailTrace_1747531 : CollatzResearch.WordTrace tailWord_1747531 prefixEnd_1747531 897323361632307510625757 := by
  unfold tailWord_1747531
  simp only [CollatzResearch.WordTrace]
  refine ⟨63737691832001116378730447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42491794554667410919153631 63737691832001116378730447)
  ·
    refine ⟨95606537748001674568095671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63737691832001116378730447 95606537748001674568095671)
    ·
      refine ⟨143409806622002511852143507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95606537748001674568095671 143409806622002511852143507)
      ·
        refine ⟨215114709933003767778215261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143409806622002511852143507 215114709933003767778215261)
        ·
          refine ⟨80668016224876412916830723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215114709933003767778215261 80668016224876412916830723)
          ·
            refine ⟨121002024337314619375246085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80668016224876412916830723 121002024337314619375246085)
            ·
              refine ⟨22687879563246491132858641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121002024337314619375246085 22687879563246491132858641)
              ·
                refine ⟨17015909672434868349643981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22687879563246491132858641 17015909672434868349643981)
                ·
                  refine ⟨6380966127163075631116493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17015909672434868349643981 6380966127163075631116493)
                  ·
                    refine ⟨2392862297686153361668685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6380966127163075631116493 2392862297686153361668685)
                    ·
                      refine ⟨897323361632307510625757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392862297686153361668685 897323361632307510625757)
                      ·
                        rfl

theorem cell23_1747531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 3].length) (baseStart_1747531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747531 prefixEnd_1747531 := by exact prefixLift 1747531
  have htrace : WordTrace (prefixWord ++ tailWord_1747531) baseStart_1747531 baseEnd_1747531 := by
    simpa [prefixWord, tailWord_1747531, baseEnd_1747531] using wordTrace_append hprefix tailTrace_1747531
  have hstable : (prefixWord ++ tailWord_1747531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747531).length < 2 ^ (prefixWord ++ tailWord_1747531).sum := by decide
  have hdescent : baseEnd_1747531 < baseStart_1747531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747532 : List Nat := [2, 2, 1, 3, 1, 2, 1, 6, 1, 2, 2]
def baseStart_1747532 : Nat := 118140960795 + 1747532 * 2 ^ 59
def prefixEnd_1747532 : Nat := 4983230072969 + 3 ^ 40 * 1747532 * 2
def baseEnd_1747532 : Nat := 897323875112962006713253

theorem tailTrace_1747532 : CollatzResearch.WordTrace tailWord_1747532 prefixEnd_1747532 897323875112962006713253 := by
  unfold tailWord_1747532
  simp only [CollatzResearch.WordTrace]
  refine ⟨31868864152498746774758425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42491818869998329033011233 31868864152498746774758425)
  ·
    refine ⟨23901648114374060081068819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31868864152498746774758425 23901648114374060081068819)
    ·
      refine ⟨35852472171561090121603229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23901648114374060081068819 35852472171561090121603229)
      ·
        refine ⟨13444677064335408795601211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35852472171561090121603229 13444677064335408795601211)
        ·
          refine ⟨20167015596503113193401817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13444677064335408795601211 20167015596503113193401817)
          ·
            refine ⟨15125261697377334895051363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20167015596503113193401817 15125261697377334895051363)
            ·
              refine ⟨22687892546066002342577045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15125261697377334895051363 22687892546066002342577045)
              ·
                refine ⟨1063494963096843859808299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22687892546066002342577045 1063494963096843859808299)
                ·
                  refine ⟨1595242444645265789712449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063494963096843859808299 1595242444645265789712449)
                  ·
                    refine ⟨1196431833483949342284337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1595242444645265789712449 1196431833483949342284337)
                    ·
                      refine ⟨897323875112962006713253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196431833483949342284337 897323875112962006713253)
                      ·
                        rfl

theorem cell23_1747532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_1747532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747532 prefixEnd_1747532 := by exact prefixLift 1747532
  have htrace : WordTrace (prefixWord ++ tailWord_1747532) baseStart_1747532 baseEnd_1747532 := by
    simpa [prefixWord, tailWord_1747532, baseEnd_1747532] using wordTrace_append hprefix tailTrace_1747532
  have hstable : (prefixWord ++ tailWord_1747532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747532).length < 2 ^ (prefixWord ++ tailWord_1747532).sum := by decide
  have hdescent : baseEnd_1747532 < baseStart_1747532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747565 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1747565 : Nat := 118140960795 + 1747565 * 2 ^ 59
def prefixEnd_1747565 : Nat := 4983230072969 + 3 ^ 40 * 1747565 * 2
def baseEnd_1747565 : Nat := 897340819974560377600601

theorem tailTrace_1747565 : CollatzResearch.WordTrace tailWord_1747565 prefixEnd_1747565 897340819974560377600601 := by
  unfold tailWord_1747565
  simp only [CollatzResearch.WordTrace]
  refine ⟨63738931913877940185468149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42492621275918626790312099 63738931913877940185468149)
  ·
    refine ⟨5975524866926056892387639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63738931913877940185468149 5975524866926056892387639)
    ·
      refine ⟨8963287300389085338581459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5975524866926056892387639 8963287300389085338581459)
      ·
        refine ⟨13444930950583628007872189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8963287300389085338581459 13444930950583628007872189)
        ·
          refine ⟨5041849106468860502952071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13444930950583628007872189 5041849106468860502952071)
          ·
            refine ⟨7562773659703290754428107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5041849106468860502952071 7562773659703290754428107)
            ·
              refine ⟨11344160489554936131642161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562773659703290754428107 11344160489554936131642161)
              ·
                refine ⟨8508120367166202098731621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11344160489554936131642161 8508120367166202098731621)
                ·
                  refine ⟨1595272568843662893512179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8508120367166202098731621 1595272568843662893512179)
                  ·
                    refine ⟨2392908853265494340268269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1595272568843662893512179 2392908853265494340268269)
                    ·
                      refine ⟨897340819974560377600601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2392908853265494340268269 897340819974560377600601)
                      ·
                        rfl

theorem cell23_1747565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1747565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747565 prefixEnd_1747565 := by exact prefixLift 1747565
  have htrace : WordTrace (prefixWord ++ tailWord_1747565) baseStart_1747565 baseEnd_1747565 := by
    simpa [prefixWord, tailWord_1747565, baseEnd_1747565] using wordTrace_append hprefix tailTrace_1747565
  have hstable : (prefixWord ++ tailWord_1747565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747565).length < 2 ^ (prefixWord ++ tailWord_1747565).sum := by decide
  have hdescent : baseEnd_1747565 < baseStart_1747565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747566 : List Nat := [4, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_1747566 : Nat := 118140960795 + 1747566 * 2 ^ 59
def prefixEnd_1747566 : Nat := 4983230072969 + 3 ^ 40 * 1747566 * 2
def baseEnd_1747566 : Nat := 897341333455214873688097

theorem tailTrace_1747566 : CollatzResearch.WordTrace tailWord_1747566 prefixEnd_1747566 897341333455214873688097 := by
  unfold tailWord_1747566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967371048359289669531819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42492645591249544904169701 7967371048359289669531819)
  ·
    refine ⟨11951056572538934504297729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7967371048359289669531819 11951056572538934504297729)
    ·
      refine ⟨8963292429404200878223297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11951056572538934504297729 8963292429404200878223297)
      ·
        refine ⟨6722469322053150658667473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8963292429404200878223297 6722469322053150658667473)
        ·
          refine ⟨5041851991539862994000605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6722469322053150658667473 5041851991539862994000605)
          ·
            refine ⟨1890694496827448622750227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5041851991539862994000605 1890694496827448622750227)
            ·
              refine ⟨2836041745241172934125341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890694496827448622750227 2836041745241172934125341)
              ·
                refine ⟨1063515654465439850297003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2836041745241172934125341 1063515654465439850297003)
                ·
                  refine ⟨1595273481698159775445505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063515654465439850297003 1595273481698159775445505)
                  ·
                    refine ⟨1196455111273619831584129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1595273481698159775445505 1196455111273619831584129)
                    ·
                      refine ⟨897341333455214873688097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196455111273619831584129 897341333455214873688097)
                      ·
                        rfl

theorem cell23_1747566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_1747566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747566 prefixEnd_1747566 := by exact prefixLift 1747566
  have htrace : WordTrace (prefixWord ++ tailWord_1747566) baseStart_1747566 baseEnd_1747566 := by
    simpa [prefixWord, tailWord_1747566, baseEnd_1747566] using wordTrace_append hprefix tailTrace_1747566
  have hstable : (prefixWord ++ tailWord_1747566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747566).length < 2 ^ (prefixWord ++ tailWord_1747566).sum := by decide
  have hdescent : baseEnd_1747566 < baseStart_1747566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747575 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 1, 3, 2]
def baseStart_1747575 : Nat := 118140960795 + 1747575 * 2 ^ 59
def prefixEnd_1747575 : Nat := 4983230072969 + 3 ^ 40 * 1747575 * 2
def baseEnd_1747575 : Nat := 897345954781105338475555

theorem tailTrace_1747575 : CollatzResearch.WordTrace tailWord_1747575 prefixEnd_1747575 897345954781105338475555 := by
  unfold tailWord_1747575
  simp only [CollatzResearch.WordTrace]
  refine ⟨63739296643841711893332179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42492864429227807928888119 63739296643841711893332179)
  ·
    refine ⟨95608944965762567839998269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63739296643841711893332179 95608944965762567839998269)
    ·
      refine ⟨35853354362160962939999351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95608944965762567839998269 35853354362160962939999351)
      ·
        refine ⟨53780031543241444409999027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35853354362160962939999351 53780031543241444409999027)
        ·
          refine ⟨80670047314862166614998541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53780031543241444409999027 80670047314862166614998541)
          ·
            refine ⟨30251267743073312480624453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80670047314862166614998541 30251267743073312480624453)
            ·
              refine ⟨5672112701826246090117085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30251267743073312480624453 5672112701826246090117085)
              ·
                refine ⟨2127042263184842283793907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5672112701826246090117085 2127042263184842283793907)
                ·
                  refine ⟨3190563394777263425690861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127042263184842283793907 3190563394777263425690861)
                  ·
                    refine ⟨1196461273041473784634073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190563394777263425690861 1196461273041473784634073)
                    ·
                      refine ⟨897345954781105338475555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196461273041473784634073 897345954781105338475555)
                      ·
                        rfl

theorem cell23_1747575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_1747575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747575 prefixEnd_1747575 := by exact prefixLift 1747575
  have htrace : WordTrace (prefixWord ++ tailWord_1747575) baseStart_1747575 baseEnd_1747575 := by
    simpa [prefixWord, tailWord_1747575, baseEnd_1747575] using wordTrace_append hprefix tailTrace_1747575
  have hstable : (prefixWord ++ tailWord_1747575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747575).length < 2 ^ (prefixWord ++ tailWord_1747575).sum := by decide
  have hdescent : baseEnd_1747575 < baseStart_1747575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747591 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1747591 : Nat := 118140960795 + 1747591 * 2 ^ 59
def prefixEnd_1747591 : Nat := 4983230072969 + 3 ^ 40 * 1747591 * 2
def baseEnd_1747591 : Nat := 897354170471577275875481

theorem tailTrace_1747591 : CollatzResearch.WordTrace tailWord_1747591 prefixEnd_1747591 897354170471577275875481 := by
  unfold tailWord_1747591
  simp only [CollatzResearch.WordTrace]
  refine ⟨63739880211783746625914627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42493253474522497750609751 63739880211783746625914627)
  ·
    refine ⟨95609820317675619938871941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63739880211783746625914627 95609820317675619938871941)
    ·
      refine ⟨17926841309564178738538489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95609820317675619938871941 17926841309564178738538489)
      ·
        refine ⟨13445130982173134053903867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17926841309564178738538489 13445130982173134053903867)
        ·
          refine ⟨20167696473259701080855801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13445130982173134053903867 20167696473259701080855801)
          ·
            refine ⟨15125772354944775810641851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20167696473259701080855801 15125772354944775810641851)
            ·
              refine ⟨22688658532417163715962777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15125772354944775810641851 22688658532417163715962777)
              ·
                refine ⟨17016493899312872786972083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22688658532417163715962777 17016493899312872786972083)
                ·
                  refine ⟨25524740848969309180458125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17016493899312872786972083 25524740848969309180458125)
                  ·
                    refine ⟨9571777818363490942671797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25524740848969309180458125 9571777818363490942671797)
                    ·
                      refine ⟨897354170471577275875481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9571777818363490942671797 897354170471577275875481)
                      ·
                        rfl

theorem cell23_1747591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1747591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747591 prefixEnd_1747591 := by exact prefixLift 1747591
  have htrace : WordTrace (prefixWord ++ tailWord_1747591) baseStart_1747591 baseEnd_1747591 := by
    simpa [prefixWord, tailWord_1747591, baseEnd_1747591] using wordTrace_append hprefix tailTrace_1747591
  have hstable : (prefixWord ++ tailWord_1747591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747591).length < 2 ^ (prefixWord ++ tailWord_1747591).sum := by decide
  have hdescent : baseEnd_1747591 < baseStart_1747591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747601 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_1747601 : Nat := 118140960795 + 1747601 * 2 ^ 59
def prefixEnd_1747601 : Nat := 4983230072969 + 3 ^ 40 * 1747601 * 2
def baseEnd_1747601 : Nat := 897359305278122236750435

theorem tailTrace_1747601 : CollatzResearch.WordTrace tailWord_1747601 prefixEnd_1747601 897359305278122236750435 := by
  unfold tailWord_1747601
  simp only [CollatzResearch.WordTrace]
  refine ⟨63740244941747518333778657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42493496627831678889185771 63740244941747518333778657)
  ·
    refine ⟨47805183706310638750333993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63740244941747518333778657 47805183706310638750333993)
    ·
      refine ⟨35853887779732979062750495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47805183706310638750333993 35853887779732979062750495)
      ·
        refine ⟨53780831669599468594125743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35853887779732979062750495 53780831669599468594125743)
        ·
          refine ⟨80671247504399202891188615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53780831669599468594125743 80671247504399202891188615)
          ·
            refine ⟨121006871256598804336782923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80671247504399202891188615 121006871256598804336782923)
            ·
              refine ⟨181510306884898206505174385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121006871256598804336782923 181510306884898206505174385)
              ·
                refine ⟨136132730163673654878880789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181510306884898206505174385 136132730163673654878880789)
                ·
                  refine ⟨6381221726422202572447537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136132730163673654878880789 6381221726422202572447537)
                  ·
                    refine ⟨4785916294816651929335653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6381221726422202572447537 4785916294816651929335653)
                    ·
                      refine ⟨897359305278122236750435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4785916294816651929335653 897359305278122236750435)
                      ·
                        rfl

theorem cell23_1747601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_1747601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747601 prefixEnd_1747601 := by exact prefixLift 1747601
  have htrace : WordTrace (prefixWord ++ tailWord_1747601) baseStart_1747601 baseEnd_1747601 := by
    simpa [prefixWord, tailWord_1747601, baseEnd_1747601] using wordTrace_append hprefix tailTrace_1747601
  have hstable : (prefixWord ++ tailWord_1747601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747601).length < 2 ^ (prefixWord ++ tailWord_1747601).sum := by decide
  have hdescent : baseEnd_1747601 < baseStart_1747601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747639 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 2, 2, 2]
def baseStart_1747639 : Nat := 118140960795 + 1747639 * 2 ^ 59
def prefixEnd_1747639 : Nat := 4983230072969 + 3 ^ 40 * 1747639 * 2
def baseEnd_1747639 : Nat := 897378817542993088075261

theorem tailTrace_1747639 : CollatzResearch.WordTrace tailWord_1747639 prefixEnd_1747639 897378817542993088075261 := by
  unfold tailWord_1747639
  simp only [CollatzResearch.WordTrace]
  refine ⟨63741630915609850823661971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42494420610406567215774647 63741630915609850823661971)
  ·
    refine ⟨95612446373414776235492957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63741630915609850823661971 95612446373414776235492957)
    ·
      refine ⟨35854667390030541088309859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95612446373414776235492957 35854667390030541088309859)
      ·
        refine ⟨53782001085045811632464789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35854667390030541088309859 53782001085045811632464789)
        ·
          refine ⟨2521031300861522420271787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53782001085045811632464789 2521031300861522420271787)
          ·
            refine ⟨3781546951292283630407681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521031300861522420271787 3781546951292283630407681)
            ·
              refine ⟨2836160213469212722805761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3781546951292283630407681 2836160213469212722805761)
              ·
                refine ⟨2127120160101909542104321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836160213469212722805761 2127120160101909542104321)
                ·
                  refine ⟨1595340120076432156578241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127120160101909542104321 1595340120076432156578241)
                  ·
                    refine ⟨1196505090057324117433681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1595340120076432156578241 1196505090057324117433681)
                    ·
                      refine ⟨897378817542993088075261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196505090057324117433681 897378817542993088075261)
                      ·
                        rfl

theorem cell23_1747639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_1747639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747639 prefixEnd_1747639 := by exact prefixLift 1747639
  have htrace : WordTrace (prefixWord ++ tailWord_1747639) baseStart_1747639 baseEnd_1747639 := by
    simpa [prefixWord, tailWord_1747639, baseEnd_1747639] using wordTrace_append hprefix tailTrace_1747639
  have hstable : (prefixWord ++ tailWord_1747639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747639).length < 2 ^ (prefixWord ++ tailWord_1747639).sum := by decide
  have hdescent : baseEnd_1747639 < baseStart_1747639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747641 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 3, 7]
def baseStart_1747641 : Nat := 118140960795 + 1747641 * 2 ^ 59
def prefixEnd_1747641 : Nat := 4983230072969 + 3 ^ 40 * 1747641 * 2
def baseEnd_1747641 : Nat := 299126614834767360083417

theorem tailTrace_1747641 : CollatzResearch.WordTrace tailWord_1747641 prefixEnd_1747641 299126614834767360083417 := by
  unfold tailWord_1747641
  simp only [CollatzResearch.WordTrace]
  refine ⟨63741703861602605165234777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42494469241068403443489851 63741703861602605165234777)
  ·
    refine ⟨47806277896201953873926083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63741703861602605165234777 47806277896201953873926083)
    ·
      refine ⟨71709416844302930810889125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47806277896201953873926083 71709416844302930810889125)
      ·
        refine ⟨13445515658306799527041711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71709416844302930810889125 13445515658306799527041711)
        ·
          refine ⟨20168273487460199290562567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13445515658306799527041711 20168273487460199290562567)
          ·
            refine ⟨30252410231190298935843851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20168273487460199290562567 30252410231190298935843851)
            ·
              refine ⟨45378615346785448403765777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30252410231190298935843851 45378615346785448403765777)
              ·
                refine ⟨34033961510089086302824333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45378615346785448403765777 34033961510089086302824333)
                ·
                  refine ⟨12762735566283407363559125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34033961510089086302824333 12762735566283407363559125)
                  ·
                    refine ⟨299126614834767360083417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12762735566283407363559125 299126614834767360083417)
                    ·
                      rfl

theorem cell23_1747641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_1747641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747641 prefixEnd_1747641 := by exact prefixLift 1747641
  have htrace : WordTrace (prefixWord ++ tailWord_1747641) baseStart_1747641 baseEnd_1747641 := by
    simpa [prefixWord, tailWord_1747641, baseEnd_1747641] using wordTrace_append hprefix tailTrace_1747641
  have hstable : (prefixWord ++ tailWord_1747641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747641).length < 2 ^ (prefixWord ++ tailWord_1747641).sum := by decide
  have hdescent : baseEnd_1747641 < baseStart_1747641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747645 : List Nat := [1, 4, 1, 2, 1, 4, 1, 4, 5]
def baseStart_1747645 : Nat := 118140960795 + 1747645 * 2 ^ 59
def prefixEnd_1747645 : Nat := 4983230072969 + 3 ^ 40 * 1747645 * 2
def baseEnd_1747645 : Nat := 99709099825213340511137

theorem tailTrace_1747645 : CollatzResearch.WordTrace tailWord_1747645 prefixEnd_1747645 99709099825213340511137 := by
  unfold tailWord_1747645
  simp only [CollatzResearch.WordTrace]
  refine ⟨63741849753588113848380389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42494566502392075898920259 63741849753588113848380389)
  ·
    refine ⟨11951596828797771346571323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63741849753588113848380389 11951596828797771346571323)
    ·
      refine ⟨17927395243196657019856985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11951596828797771346571323 17927395243196657019856985)
      ·
        refine ⟨13445546432397492764892739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17927395243196657019856985 13445546432397492764892739)
        ·
          refine ⟨20168319648596239147339109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13445546432397492764892739 20168319648596239147339109)
          ·
            refine ⟨3781559934111794840126083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20168319648596239147339109 3781559934111794840126083)
            ·
              refine ⟨5672339901167692260189125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781559934111794840126083 5672339901167692260189125)
              ·
                refine ⟨1063563731468942298785461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5672339901167692260189125 1063563731468942298785461)
                ·
                  refine ⟨99709099825213340511137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1063563731468942298785461 99709099825213340511137)
                  ·
                    rfl

theorem cell23_1747645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_1747645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747645 prefixEnd_1747645 := by exact prefixLift 1747645
  have htrace : WordTrace (prefixWord ++ tailWord_1747645) baseStart_1747645 baseEnd_1747645 := by
    simpa [prefixWord, tailWord_1747645, baseEnd_1747645] using wordTrace_append hprefix tailTrace_1747645
  have hstable : (prefixWord ++ tailWord_1747645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747645).length < 2 ^ (prefixWord ++ tailWord_1747645).sum := by decide
  have hdescent : baseEnd_1747645 < baseStart_1747645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747695 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 2, 4, 2]
def baseStart_1747695 : Nat := 118140960795 + 1747695 * 2 ^ 59
def prefixEnd_1747695 : Nat := 4983230072969 + 3 ^ 40 * 1747695 * 2
def baseEnd_1747695 : Nat := 897407572459644868975003

theorem tailTrace_1747695 : CollatzResearch.WordTrace tailWord_1747695 prefixEnd_1747695 897407572459644868975003 := by
  unfold tailWord_1747695
  simp only [CollatzResearch.WordTrace]
  refine ⟨63743673403406972387700539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42495782268937981591800359 63743673403406972387700539)
  ·
    refine ⟨95615510105110458581550809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63743673403406972387700539 95615510105110458581550809)
    ·
      refine ⟨71711632578832843936163107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95615510105110458581550809 71711632578832843936163107)
      ·
        refine ⟨107567448868249265904244661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71711632578832843936163107 107567448868249265904244661)
        ·
          refine ⟨10084448331398368678522937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107567448868249265904244661 10084448331398368678522937)
          ·
            refine ⟨7563336248548776508892203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10084448331398368678522937 7563336248548776508892203)
            ·
              refine ⟨11345004372823164763338305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7563336248548776508892203 11345004372823164763338305)
              ·
                refine ⟨8508753279617373572503729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11345004372823164763338305 8508753279617373572503729)
                ·
                  refine ⟨6381564959713030179377797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508753279617373572503729 6381564959713030179377797)
                  ·
                    refine ⟨1196543429946193158633337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381564959713030179377797 1196543429946193158633337)
                    ·
                      refine ⟨897407572459644868975003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196543429946193158633337 897407572459644868975003)
                      ·
                        rfl

theorem cell23_1747695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4, 2].length) (baseStart_1747695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747695 prefixEnd_1747695 := by exact prefixLift 1747695
  have htrace : WordTrace (prefixWord ++ tailWord_1747695) baseStart_1747695 baseEnd_1747695 := by
    simpa [prefixWord, tailWord_1747695, baseEnd_1747695] using wordTrace_append hprefix tailTrace_1747695
  have hstable : (prefixWord ++ tailWord_1747695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747695).length < 2 ^ (prefixWord ++ tailWord_1747695).sum := by decide
  have hdescent : baseEnd_1747695 < baseStart_1747695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747755 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 4, 3, 2]
def baseStart_1747755 : Nat := 118140960795 + 1747755 * 2 ^ 59
def prefixEnd_1747755 : Nat := 4983230072969 + 3 ^ 40 * 1747755 * 2
def baseEnd_1747755 : Nat := 897438381298914634224727

theorem tailTrace_1747755 : CollatzResearch.WordTrace tailWord_1747755 prefixEnd_1747755 897438381298914634224727 := by
  unfold tailWord_1747755
  simp only [CollatzResearch.WordTrace]
  refine ⟨63745861783189602634884719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42497241188793068423256479 63745861783189602634884719)
  ·
    refine ⟨95618792674784403952327079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63745861783189602634884719 95618792674784403952327079)
    ·
      refine ⟨143428189012176605928490619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95618792674784403952327079 143428189012176605928490619)
      ·
        refine ⟨215142283518264908892735929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143428189012176605928490619 215142283518264908892735929)
        ·
          refine ⟨161356712638698681669551947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215142283518264908892735929 161356712638698681669551947)
          ·
            refine ⟨242035068958048022504327921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161356712638698681669551947 242035068958048022504327921)
            ·
              refine ⟨181526301718536016878245941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242035068958048022504327921 181526301718536016878245941)
              ·
                refine ⟨17018090786112751582335557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181526301718536016878245941 17018090786112751582335557)
                ·
                  refine ⟨3190892022396140921687917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17018090786112751582335557 3190892022396140921687917)
                  ·
                    refine ⟨1196584508398552845632969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3190892022396140921687917 1196584508398552845632969)
                    ·
                      refine ⟨897438381298914634224727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196584508398552845632969 897438381298914634224727)
                      ·
                        rfl

theorem cell23_1747755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3, 2].length) (baseStart_1747755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747755 prefixEnd_1747755 := by exact prefixLift 1747755
  have htrace : WordTrace (prefixWord ++ tailWord_1747755) baseStart_1747755 baseEnd_1747755 := by
    simpa [prefixWord, tailWord_1747755, baseEnd_1747755] using wordTrace_append hprefix tailTrace_1747755
  have hstable : (prefixWord ++ tailWord_1747755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747755).length < 2 ^ (prefixWord ++ tailWord_1747755).sum := by decide
  have hdescent : baseEnd_1747755 < baseStart_1747755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747785 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_1747785 : Nat := 118140960795 + 1747785 * 2 ^ 59
def prefixEnd_1747785 : Nat := 4983230072969 + 3 ^ 40 * 1747785 * 2
def baseEnd_1747785 : Nat := 897453785718549516849589

theorem tailTrace_1747785 : CollatzResearch.WordTrace tailWord_1747785 prefixEnd_1747785 897453785718549516849589 := by
  unfold tailWord_1747785
  simp only [CollatzResearch.WordTrace]
  refine ⟨63746955973080917758476809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42497970648720611838984539 63746955973080917758476809)
  ·
    refine ⟨47810216979810688318857607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63746955973080917758476809 47810216979810688318857607)
    ·
      refine ⟨71715325469716032478286411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47810216979810688318857607 71715325469716032478286411)
      ·
        refine ⟨107572988204574048717429617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71715325469716032478286411 107572988204574048717429617)
        ·
          refine ⟨80679741153430536538072213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107572988204574048717429617 80679741153430536538072213)
          ·
            refine ⟨3781862866567056400222135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80679741153430536538072213 3781862866567056400222135)
            ·
              refine ⟨5672794299850584600333203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781862866567056400222135 5672794299850584600333203)
              ·
                refine ⟨8509191449775876900499805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5672794299850584600333203 8509191449775876900499805)
                ·
                  refine ⟨3190946793665953837687427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8509191449775876900499805 3190946793665953837687427)
                  ·
                    refine ⟨4786420190498930756531141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3190946793665953837687427 4786420190498930756531141)
                    ·
                      refine ⟨897453785718549516849589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4786420190498930756531141 897453785718549516849589)
                      ·
                        rfl

theorem cell23_1747785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_1747785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747785 prefixEnd_1747785 := by exact prefixLift 1747785
  have htrace : WordTrace (prefixWord ++ tailWord_1747785) baseStart_1747785 baseEnd_1747785 := by
    simpa [prefixWord, tailWord_1747785, baseEnd_1747785] using wordTrace_append hprefix tailTrace_1747785
  have hstable : (prefixWord ++ tailWord_1747785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747785).length < 2 ^ (prefixWord ++ tailWord_1747785).sum := by decide
  have hdescent : baseEnd_1747785 < baseStart_1747785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747812 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_1747812 : Nat := 118140960795 + 1747812 * 2 ^ 59
def prefixEnd_1747812 : Nat := 4983230072969 + 3 ^ 40 * 1747812 * 2
def baseEnd_1747812 : Nat := 299155883232073637070655

theorem tailTrace_1747812 : CollatzResearch.WordTrace tailWord_1747812 prefixEnd_1747812 299155883232073637070655 := by
  unfold tailWord_1747812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31873970371991550684854845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42498627162655400913139793 31873970371991550684854845)
  ·
    refine ⟨11952738889496831506820567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31873970371991550684854845 11952738889496831506820567)
    ·
      refine ⟨17929108334245247260230851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11952738889496831506820567 17929108334245247260230851)
      ·
        refine ⟨26893662501367870890346277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17929108334245247260230851 26893662501367870890346277)
        ·
          refine ⟨5042561719006475791939927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26893662501367870890346277 5042561719006475791939927)
          ·
            refine ⟨7563842578509713687909891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042561719006475791939927 7563842578509713687909891)
            ·
              refine ⟨11345763867764570531864837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7563842578509713687909891 11345763867764570531864837)
              ·
                refine ⟨2127330725205856974724657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11345763867764570531864837 2127330725205856974724657)
                ·
                  refine ⟨1595498043904392731043493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127330725205856974724657 1595498043904392731043493)
                  ·
                    refine ⟨299155883232073637070655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595498043904392731043493 299155883232073637070655)
                    ·
                      rfl

theorem cell23_1747812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_1747812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747812 prefixEnd_1747812 := by exact prefixLift 1747812
  have htrace : WordTrace (prefixWord ++ tailWord_1747812) baseStart_1747812 baseEnd_1747812 := by
    simpa [prefixWord, tailWord_1747812, baseEnd_1747812] using wordTrace_append hprefix tailTrace_1747812
  have hstable : (prefixWord ++ tailWord_1747812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747812).length < 2 ^ (prefixWord ++ tailWord_1747812).sum := by decide
  have hdescent : baseEnd_1747812 < baseStart_1747812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747825 : List Nat := [1, 2, 2, 2, 1, 6, 1, 8]
def baseStart_1747825 : Nat := 118140960795 + 1747825 * 2 ^ 59
def prefixEnd_1747825 : Nat := 4983230072969 + 3 ^ 40 * 1747825 * 2
def baseEnd_1747825 : Nat := 33239789812767754087015

theorem tailTrace_1747825 : CollatzResearch.WordTrace tailWord_1747825 prefixEnd_1747825 33239789812767754087015 := by
  unfold tailWord_1747825
  simp only [CollatzResearch.WordTrace]
  refine ⟨63748414892936004589932929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42498943261957336393288619 63748414892936004589932929)
  ·
    refine ⟨47811311169702003442449697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63748414892936004589932929 47811311169702003442449697)
    ·
      refine ⟨35858483377276502581837273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47811311169702003442449697 35858483377276502581837273)
      ·
        refine ⟨26893862532957376936377955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35858483377276502581837273 26893862532957376936377955)
        ·
          refine ⟨40340793799436065404566933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26893862532957376936377955 40340793799436065404566933)
          ·
            refine ⟨1890974709348565565839075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40340793799436065404566933 1890974709348565565839075)
            ·
              refine ⟨2836462064022848348758613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890974709348565565839075 2836462064022848348758613)
              ·
                refine ⟨33239789812767754087015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2836462064022848348758613 33239789812767754087015)
                ·
                  rfl

theorem cell23_1747825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 8].length) (baseStart_1747825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747825 prefixEnd_1747825 := by exact prefixLift 1747825
  have htrace : WordTrace (prefixWord ++ tailWord_1747825) baseStart_1747825 baseEnd_1747825 := by
    simpa [prefixWord, tailWord_1747825, baseEnd_1747825] using wordTrace_append hprefix tailTrace_1747825
  have hstable : (prefixWord ++ tailWord_1747825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747825).length < 2 ^ (prefixWord ++ tailWord_1747825).sum := by decide
  have hdescent : baseEnd_1747825 < baseStart_1747825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747835 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 3]
def baseStart_1747835 : Nat := 118140960795 + 1747835 * 2 ^ 59
def prefixEnd_1747835 : Nat := 4983230072969 + 3 ^ 40 * 1747835 * 2
def baseEnd_1747835 : Nat := 897479459751274321224359

theorem tailTrace_1747835 : CollatzResearch.WordTrace tailWord_1747835 prefixEnd_1747835 897479459751274321224359 := by
  unfold tailWord_1747835
  simp only [CollatzResearch.WordTrace]
  refine ⟨63748779622899776297796959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42499186415266517531864639 63748779622899776297796959)
  ·
    refine ⟨95623169434349664446695439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63748779622899776297796959 95623169434349664446695439)
    ·
      refine ⟨143434754151524496670043159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95623169434349664446695439 143434754151524496670043159)
      ·
        refine ⟨215152131227286745005064739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143434754151524496670043159 215152131227286745005064739)
        ·
          refine ⟨322728196840930117507597109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215152131227286745005064739 322728196840930117507597109)
          ·
            refine ⟨30255768453837198516337229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 322728196840930117507597109 30255768453837198516337229)
            ·
              refine ⟨11345913170188949443626461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30255768453837198516337229 11345913170188949443626461)
              ·
                refine ⟨4254717438820856041359923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11345913170188949443626461 4254717438820856041359923)
                ·
                  refine ⟨6382076158231284062039885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4254717438820856041359923 6382076158231284062039885)
                  ·
                    refine ⟨2393278559336731523264957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6382076158231284062039885 2393278559336731523264957)
                    ·
                      refine ⟨897479459751274321224359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2393278559336731523264957 897479459751274321224359)
                      ·
                        rfl

theorem cell23_1747835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 3].length) (baseStart_1747835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747835 prefixEnd_1747835 := by exact prefixLift 1747835
  have htrace : WordTrace (prefixWord ++ tailWord_1747835) baseStart_1747835 baseEnd_1747835 := by
    simpa [prefixWord, tailWord_1747835, baseEnd_1747835] using wordTrace_append hprefix tailTrace_1747835
  have hstable : (prefixWord ++ tailWord_1747835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747835).length < 2 ^ (prefixWord ++ tailWord_1747835).sum := by decide
  have hdescent : baseEnd_1747835 < baseStart_1747835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747888 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_1747888 : Nat := 118140960795 + 1747888 * 2 ^ 59
def prefixEnd_1747888 : Nat := 4983230072969 + 3 ^ 40 * 1747888 * 2
def baseEnd_1747888 : Nat := 897506674225962613861615

theorem tailTrace_1747888 : CollatzResearch.WordTrace tailWord_1747888 prefixEnd_1747888 897506674225962613861615 := by
  unfold tailWord_1747888
  simp only [CollatzResearch.WordTrace]
  refine ⟨31875356345853883174738159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42500475127805177566317545 31875356345853883174738159)
  ·
    refine ⟨47813034518780824762107239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31875356345853883174738159 47813034518780824762107239)
    ·
      refine ⟨71719551778171237143160859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47813034518780824762107239 71719551778171237143160859)
      ·
        refine ⟨107579327667256855714741289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71719551778171237143160859 107579327667256855714741289)
        ·
          refine ⟨80684495750442641786055967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107579327667256855714741289 80684495750442641786055967)
          ·
            refine ⟨121026743625663962679083951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80684495750442641786055967 121026743625663962679083951)
            ·
              refine ⟨181540115438495944018625927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121026743625663962679083951 181540115438495944018625927)
              ·
                refine ⟨272310173157743916027938891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181540115438495944018625927 272310173157743916027938891)
                ·
                  refine ⟨408465259736615874041908337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272310173157743916027938891 408465259736615874041908337)
                  ·
                    refine ⟨306348944802461905531431253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 408465259736615874041908337 306348944802461905531431253)
                    ·
                      refine ⟨897506674225962613861615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 306348944802461905531431253 897506674225962613861615)
                      ·
                        rfl

theorem cell23_1747888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_1747888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747888 prefixEnd_1747888 := by exact prefixLift 1747888
  have htrace : WordTrace (prefixWord ++ tailWord_1747888) baseStart_1747888 baseEnd_1747888 := by
    simpa [prefixWord, tailWord_1747888, baseEnd_1747888] using wordTrace_append hprefix tailTrace_1747888
  have hstable : (prefixWord ++ tailWord_1747888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747888).length < 2 ^ (prefixWord ++ tailWord_1747888).sum := by decide
  have hdescent : baseEnd_1747888 < baseStart_1747888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747895 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_1747895 : Nat := 118140960795 + 1747895 * 2 ^ 59
def prefixEnd_1747895 : Nat := 4983230072969 + 3 ^ 40 * 1747895 * 2
def baseEnd_1747895 : Nat := 897510268590544086474083

theorem tailTrace_1747895 : CollatzResearch.WordTrace tailWord_1747895 prefixEnd_1747895 897510268590544086474083 := by
  unfold tailWord_1747895
  simp only [CollatzResearch.WordTrace]
  refine ⟨63750968002682406544981139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42500645335121604363320759 63750968002682406544981139)
  ·
    refine ⟨95626452004023609817471709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63750968002682406544981139 95626452004023609817471709)
    ·
      refine ⟨35859919501508853681551891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95626452004023609817471709 35859919501508853681551891)
      ·
        refine ⟨53789879252263280522327837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35859919501508853681551891 53789879252263280522327837)
        ·
          refine ⟨20171204719598730195872939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53789879252263280522327837 20171204719598730195872939)
          ·
            refine ⟨30256807079398095293809409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20171204719598730195872939 30256807079398095293809409)
            ·
              refine ⟨22692605309548571470357057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30256807079398095293809409 22692605309548571470357057)
              ·
                refine ⟨17019453982161428602767793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22692605309548571470357057 17019453982161428602767793)
                ·
                  refine ⟨12764590486621071452075845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17019453982161428602767793 12764590486621071452075845)
                  ·
                    refine ⟨2393360716241450897264221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12764590486621071452075845 2393360716241450897264221)
                    ·
                      refine ⟨897510268590544086474083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2393360716241450897264221 897510268590544086474083)
                      ·
                        rfl

theorem cell23_1747895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_1747895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747895 prefixEnd_1747895 := by exact prefixLift 1747895
  have htrace : WordTrace (prefixWord ++ tailWord_1747895) baseStart_1747895 baseEnd_1747895 := by
    simpa [prefixWord, tailWord_1747895, baseEnd_1747895] using wordTrace_append hprefix tailTrace_1747895
  have hstable : (prefixWord ++ tailWord_1747895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747895).length < 2 ^ (prefixWord ++ tailWord_1747895).sum := by decide
  have hdescent : baseEnd_1747895 < baseStart_1747895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747912 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_1747912 : Nat := 118140960795 + 1747912 * 2 ^ 59
def prefixEnd_1747912 : Nat := 4983230072969 + 3 ^ 40 * 1747912 * 2
def baseEnd_1747912 : Nat := 897518997761670519961505

theorem tailTrace_1747912 : CollatzResearch.WordTrace tailWord_1747912 prefixEnd_1747912 897518997761670519961505 := by
  unfold tailWord_1747912
  simp only [CollatzResearch.WordTrace]
  refine ⟨31875794021810409224174995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42501058695747212298899993 31875794021810409224174995)
  ·
    refine ⟨47813691032715613836262493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31875794021810409224174995 47813691032715613836262493)
    ·
      refine ⟨17930134137268355188598435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47813691032715613836262493 17930134137268355188598435)
      ·
        refine ⟨26895201205902532782897653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17930134137268355188598435 26895201205902532782897653)
        ·
          refine ⟨2521425113053362448396655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26895201205902532782897653 2521425113053362448396655)
          ·
            refine ⟨3782137669580043672594983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521425113053362448396655 3782137669580043672594983)
            ·
              refine ⟨5673206504370065508892475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782137669580043672594983 5673206504370065508892475)
              ·
                refine ⟨8509809756555098263338713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673206504370065508892475 8509809756555098263338713)
                ·
                  refine ⟨6382357317416323697504035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8509809756555098263338713 6382357317416323697504035)
                  ·
                    refine ⟨9573535976124485546256053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6382357317416323697504035 9573535976124485546256053)
                    ·
                      refine ⟨897518997761670519961505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9573535976124485546256053 897518997761670519961505)
                      ·
                        rfl

theorem cell23_1747912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_1747912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747912 prefixEnd_1747912 := by exact prefixLift 1747912
  have htrace : WordTrace (prefixWord ++ tailWord_1747912) baseStart_1747912 baseEnd_1747912 := by
    simpa [prefixWord, tailWord_1747912, baseEnd_1747912] using wordTrace_append hprefix tailTrace_1747912
  have hstable : (prefixWord ++ tailWord_1747912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747912).length < 2 ^ (prefixWord ++ tailWord_1747912).sum := by decide
  have hdescent : baseEnd_1747912 < baseStart_1747912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747943 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_1747943 : Nat := 118140960795 + 1747943 * 2 ^ 59
def prefixEnd_1747943 : Nat := 4983230072969 + 3 ^ 40 * 1747943 * 2
def baseEnd_1747943 : Nat := 897534915661959898673863

theorem tailTrace_1747943 : CollatzResearch.WordTrace tailWord_1747943 prefixEnd_1747943 897534915661959898673863 := by
  unfold tailWord_1747943
  simp only [CollatzResearch.WordTrace]
  refine ⟨63752718706508510742728483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42501812471005673828485655 63752718706508510742728483)
  ·
    refine ⟨95629078059762766114092725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63752718706508510742728483 95629078059762766114092725)
    ·
      refine ⟨8965226068102759323196193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95629078059762766114092725 8965226068102759323196193)
      ·
        refine ⟨6723919551077069492397145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8965226068102759323196193 6723919551077069492397145)
        ·
          refine ⟨5042939663307802119297859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6723919551077069492397145 5042939663307802119297859)
          ·
            refine ⟨7564409494961703178946789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042939663307802119297859 7564409494961703178946789)
            ·
              refine ⟨1418326780305319346052523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7564409494961703178946789 1418326780305319346052523)
              ·
                refine ⟨2127490170457979019078785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418326780305319346052523 2127490170457979019078785)
                ·
                  refine ⟨1595617627843484264309089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127490170457979019078785 1595617627843484264309089)
                  ·
                    refine ⟨1196713220882613198231817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1595617627843484264309089 1196713220882613198231817)
                    ·
                      refine ⟨897534915661959898673863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196713220882613198231817 897534915661959898673863)
                      ·
                        rfl

theorem cell23_1747943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_1747943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747943 prefixEnd_1747943 := by exact prefixLift 1747943
  have htrace : WordTrace (prefixWord ++ tailWord_1747943) baseStart_1747943 baseEnd_1747943 := by
    simpa [prefixWord, tailWord_1747943, baseEnd_1747943] using wordTrace_append hprefix tailTrace_1747943
  have hstable : (prefixWord ++ tailWord_1747943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747943).length < 2 ^ (prefixWord ++ tailWord_1747943).sum := by decide
  have hdescent : baseEnd_1747943 < baseStart_1747943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747999 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 2, 4, 2]
def baseStart_1747999 : Nat := 118140960795 + 1747999 * 2 ^ 59
def prefixEnd_1747999 : Nat := 4983230072969 + 3 ^ 40 * 1747999 * 2
def baseEnd_1747999 : Nat := 897563670578611679573605

theorem tailTrace_1747999 : CollatzResearch.WordTrace tailWord_1747999 prefixEnd_1747999 897563670578611679573605 := by
  unfold tailWord_1747999
  simp only [CollatzResearch.WordTrace]
  refine ⟨63754761194305632306767051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42503174129537088204511367 63754761194305632306767051)
  ·
    refine ⟨95632141791458448460150577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63754761194305632306767051 95632141791458448460150577)
    ·
      refine ⟨71724106343593836345112933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95632141791458448460150577 71724106343593836345112933)
      ·
        refine ⟨13448269939423844314708675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71724106343593836345112933 13448269939423844314708675)
        ·
          refine ⟨20172404909135766472063013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13448269939423844314708675 20172404909135766472063013)
          ·
            refine ⟨3782325920462956213511815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20172404909135766472063013 3782325920462956213511815)
            ·
              refine ⟨5673488880694434320267723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782325920462956213511815 5673488880694434320267723)
              ·
                refine ⟨8510233321041651480401585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673488880694434320267723 8510233321041651480401585)
                ·
                  refine ⟨6382674990781238610301189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8510233321041651480401585 6382674990781238610301189)
                  ·
                    refine ⟨1196751560771482239431473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382674990781238610301189 1196751560771482239431473)
                    ·
                      refine ⟨897563670578611679573605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196751560771482239431473 897563670578611679573605)
                      ·
                        rfl

theorem cell23_1747999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_1747999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1747999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1747999 prefixEnd_1747999 := by exact prefixLift 1747999
  have htrace : WordTrace (prefixWord ++ tailWord_1747999) baseStart_1747999 baseEnd_1747999 := by
    simpa [prefixWord, tailWord_1747999, baseEnd_1747999] using wordTrace_append hprefix tailTrace_1747999
  have hstable : (prefixWord ++ tailWord_1747999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747999).length < 2 ^ (prefixWord ++ tailWord_1747999).sum := by decide
  have hdescent : baseEnd_1747999 < baseStart_1747999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748039 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 6]
def baseStart_1748039 : Nat := 118140960795 + 1748039 * 2 ^ 59
def prefixEnd_1748039 : Nat := 4983230072969 + 3 ^ 40 * 1748039 * 2
def baseEnd_1748039 : Nat := 99731578867199058119269

theorem tailTrace_1748039 : CollatzResearch.WordTrace tailWord_1748039 prefixEnd_1748039 99731578867199058119269 := by
  unfold tailWord_1748039
  simp only [CollatzResearch.WordTrace]
  refine ⟨63756220114160719138223171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42504146742773812758815447 63756220114160719138223171)
  ·
    refine ⟨95634330171241078707334757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63756220114160719138223171 95634330171241078707334757)
    ·
      refine ⟨17931436907107702257625267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95634330171241078707334757 17931436907107702257625267)
      ·
        refine ⟨26897155360661553386437901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17931436907107702257625267 26897155360661553386437901)
        ·
          refine ⟨10086433260248082519914213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26897155360661553386437901 10086433260248082519914213)
          ·
            refine ⟨1891206236296515472483915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10086433260248082519914213 1891206236296515472483915)
            ·
              refine ⟨2836809354444773208725873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891206236296515472483915 2836809354444773208725873)
              ·
                refine ⟨2127607015833579906544405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836809354444773208725873 2127607015833579906544405)
                ·
                  refine ⟨99731578867199058119269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2127607015833579906544405 99731578867199058119269)
                  ·
                    rfl

theorem cell23_1748039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 6].length) (baseStart_1748039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748039 prefixEnd_1748039 := by exact prefixLift 1748039
  have htrace : WordTrace (prefixWord ++ tailWord_1748039) baseStart_1748039 baseEnd_1748039 := by
    simpa [prefixWord, tailWord_1748039, baseEnd_1748039] using wordTrace_append hprefix tailTrace_1748039
  have hstable : (prefixWord ++ tailWord_1748039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748039).length < 2 ^ (prefixWord ++ tailWord_1748039).sum := by decide
  have hdescent : baseEnd_1748039 < baseStart_1748039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748049 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_1748049 : Nat := 118140960795 + 1748049 * 2 ^ 59
def prefixEnd_1748049 : Nat := 4983230072969 + 3 ^ 40 * 1748049 * 2
def baseEnd_1748049 : Nat := 897589344611336483948375

theorem tailTrace_1748049 : CollatzResearch.WordTrace tailWord_1748049 prefixEnd_1748049 897589344611336483948375 := by
  unfold tailWord_1748049
  simp only [CollatzResearch.WordTrace]
  refine ⟨63756584844124490846087201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42504389896082993897391467 63756584844124490846087201)
  ·
    refine ⟨47817438633093368134565401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63756584844124490846087201 47817438633093368134565401)
    ·
      refine ⟨35863078974820026100924051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47817438633093368134565401 35863078974820026100924051)
      ·
        refine ⟨53794618462230039151386077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35863078974820026100924051 53794618462230039151386077)
        ·
          refine ⟨20172981923336264681769779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53794618462230039151386077 20172981923336264681769779)
          ·
            refine ⟨30259472885004397022654669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20172981923336264681769779 30259472885004397022654669)
            ·
              refine ⟨11347302331876648883495501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30259472885004397022654669 11347302331876648883495501)
              ·
                refine ⟨4255238374453743331310813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11347302331876648883495501 4255238374453743331310813)
                ·
                  refine ⟨1595714390420153749241555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4255238374453743331310813 1595714390420153749241555)
                  ·
                    refine ⟨2393571585630230623862333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1595714390420153749241555 2393571585630230623862333)
                    ·
                      refine ⟨897589344611336483948375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2393571585630230623862333 897589344611336483948375)
                      ·
                        rfl

theorem cell23_1748049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_1748049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748049 prefixEnd_1748049 := by exact prefixLift 1748049
  have htrace : WordTrace (prefixWord ++ tailWord_1748049) baseStart_1748049 baseEnd_1748049 := by
    simpa [prefixWord, tailWord_1748049, baseEnd_1748049] using wordTrace_append hprefix tailTrace_1748049
  have hstable : (prefixWord ++ tailWord_1748049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748049).length < 2 ^ (prefixWord ++ tailWord_1748049).sum := by decide
  have hdescent : baseEnd_1748049 < baseStart_1748049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748052 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1748052 : Nat := 118140960795 + 1748052 * 2 ^ 59
def prefixEnd_1748052 : Nat := 4983230072969 + 3 ^ 40 * 1748052 * 2
def baseEnd_1748052 : Nat := 299196961684433324070287

theorem tailTrace_1748052 : CollatzResearch.WordTrace tailWord_1748052 prefixEnd_1748052 299196961684433324070287 := by
  unfold tailWord_1748052
  simp only [CollatzResearch.WordTrace]
  refine ⟨31878347131556811179223205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42504462842075748238964273 31878347131556811179223205)
  ·
    refine ⟨5977190087166902096104351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31878347131556811179223205 5977190087166902096104351)
    ·
      refine ⟨8965785130750353144156527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5977190087166902096104351 8965785130750353144156527)
      ·
        refine ⟨13448677696125529716234791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8965785130750353144156527 13448677696125529716234791)
        ·
          refine ⟨20173016544188294574352187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13448677696125529716234791 20173016544188294574352187)
          ·
            refine ⟨30259524816282441861528281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20173016544188294574352187 30259524816282441861528281)
            ·
              refine ⟨22694643612211831396146211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30259524816282441861528281 22694643612211831396146211)
              ·
                refine ⟨34041965418317747094219317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22694643612211831396146211 34041965418317747094219317)
                ·
                  refine ⟨3191434257967288790083061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34041965418317747094219317 3191434257967288790083061)
                  ·
                    refine ⟨299196961684433324070287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3191434257967288790083061 299196961684433324070287)
                    ·
                      rfl

theorem cell23_1748052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1748052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748052 prefixEnd_1748052 := by exact prefixLift 1748052
  have htrace : WordTrace (prefixWord ++ tailWord_1748052) baseStart_1748052 baseEnd_1748052 := by
    simpa [prefixWord, tailWord_1748052, baseEnd_1748052] using wordTrace_append hprefix tailTrace_1748052
  have hstable : (prefixWord ++ tailWord_1748052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748052).length < 2 ^ (prefixWord ++ tailWord_1748052).sum := by decide
  have hdescent : baseEnd_1748052 < baseStart_1748052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748069 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_1748069 : Nat := 118140960795 + 1748069 * 2 ^ 59
def prefixEnd_1748069 : Nat := 4983230072969 + 3 ^ 40 * 1748069 * 2
def baseEnd_1748069 : Nat := 299199871408142135232761

theorem tailTrace_1748069 : CollatzResearch.WordTrace tailWord_1748069 prefixEnd_1748069 299199871408142135232761 := by
  unfold tailWord_1748069
  simp only [CollatzResearch.WordTrace]
  refine ⟨63757314304052034261815261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42504876202701356174543507 63757314304052034261815261)
  ·
    refine ⟨23908992864019512848180723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63757314304052034261815261 23908992864019512848180723)
    ·
      refine ⟨35863489296029269272271085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23908992864019512848180723 35863489296029269272271085)
      ·
        refine ⟨13448808486010975977101657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35863489296029269272271085 13448808486010975977101657)
        ·
          refine ⟨10086606364508231982826243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13448808486010975977101657 10086606364508231982826243)
          ·
            refine ⟨15129909546762347974239365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086606364508231982826243 15129909546762347974239365)
            ·
              refine ⟨2836858040017940245169881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15129909546762347974239365 2836858040017940245169881)
              ·
                refine ⟨2127643530013455183877411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836858040017940245169881 2127643530013455183877411)
                ·
                  refine ⟨3191465295020182775816117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127643530013455183877411 3191465295020182775816117)
                  ·
                    refine ⟨299199871408142135232761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3191465295020182775816117 299199871408142135232761)
                    ·
                      rfl

theorem cell23_1748069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_1748069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748069 prefixEnd_1748069 := by exact prefixLift 1748069
  have htrace : WordTrace (prefixWord ++ tailWord_1748069) baseStart_1748069 baseEnd_1748069 := by
    simpa [prefixWord, tailWord_1748069, baseEnd_1748069] using wordTrace_append hprefix tailTrace_1748069
  have hstable : (prefixWord ++ tailWord_1748069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748069).length < 2 ^ (prefixWord ++ tailWord_1748069).sum := by decide
  have hdescent : baseEnd_1748069 < baseStart_1748069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748082 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_1748082 : Nat := 118140960795 + 1748082 * 2 ^ 59
def prefixEnd_1748082 : Nat := 4983230072969 + 3 ^ 40 * 1748082 * 2
def baseEnd_1748082 : Nat := 299202096490978284945241

theorem tailTrace_1748082 : CollatzResearch.WordTrace tailWord_1748082 prefixEnd_1748082 299202096490978284945241 := by
  unfold tailWord_1748082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15939447113251234370509625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42505192302003291654692333 15939447113251234370509625)
  ·
    refine ⟨11954585334938425777882219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15939447113251234370509625 11954585334938425777882219)
    ·
      refine ⟨17931878002407638666823329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11954585334938425777882219 17931878002407638666823329)
      ·
        refine ⟨13448908501805729000117497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17931878002407638666823329 13448908501805729000117497)
        ·
          refine ⟨10086681376354296750088123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13448908501805729000117497 10086681376354296750088123)
          ·
            refine ⟨15130022064531445125132185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086681376354296750088123 15130022064531445125132185)
            ·
              refine ⟨11347516548398583843849139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15130022064531445125132185 11347516548398583843849139)
              ·
                refine ⟨17021274822597875765773709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11347516548398583843849139 17021274822597875765773709)
                ·
                  refine ⟨6382978058474203412165141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17021274822597875765773709 6382978058474203412165141)
                  ·
                    refine ⟨299202096490978284945241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6382978058474203412165141 299202096490978284945241)
                    ·
                      rfl

theorem cell23_1748082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_1748082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748082 prefixEnd_1748082 := by exact prefixLift 1748082
  have htrace : WordTrace (prefixWord ++ tailWord_1748082) baseStart_1748082 baseEnd_1748082 := by
    simpa [prefixWord, tailWord_1748082, baseEnd_1748082] using wordTrace_append hprefix tailTrace_1748082
  have hstable : (prefixWord ++ tailWord_1748082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748082).length < 2 ^ (prefixWord ++ tailWord_1748082).sum := by decide
  have hdescent : baseEnd_1748082 < baseStart_1748082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748094 : List Nat := [4, 2, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1748094 : Nat := 118140960795 + 1748094 * 2 ^ 59
def prefixEnd_1748094 : Nat := 4983230072969 + 3 ^ 40 * 1748094 * 2
def baseEnd_1748094 : Nat := 299204150413596269295223

theorem tailTrace_1748094 : CollatzResearch.WordTrace tailWord_1748094 prefixEnd_1748094 299204150413596269295223 := by
  unfold tailWord_1748094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969778266120182941434417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42505484085974309020983557 7969778266120182941434417)
  ·
    refine ⟨5977333699590137206075813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7969778266120182941434417 5977333699590137206075813)
    ·
      refine ⟨1120750068673150726139215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5977333699590137206075813 1120750068673150726139215)
      ·
        refine ⟨1681125103009726089208823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120750068673150726139215 1681125103009726089208823)
        ·
          refine ⟨2521687654514589133813235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681125103009726089208823 2521687654514589133813235)
          ·
            refine ⟨3782531481771883700719853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521687654514589133813235 3782531481771883700719853)
            ·
              refine ⟨1418449305664456387769945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3782531481771883700719853 1418449305664456387769945)
              ·
                refine ⟨1063836979248342290827459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418449305664456387769945 1063836979248342290827459)
                ·
                  refine ⟨1595755468872513436241189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063836979248342290827459 1595755468872513436241189)
                  ·
                    refine ⟨299204150413596269295223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595755468872513436241189 299204150413596269295223)
                    ·
                      rfl

theorem cell23_1748094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1748094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748094 prefixEnd_1748094 := by exact prefixLift 1748094
  have htrace : WordTrace (prefixWord ++ tailWord_1748094) baseStart_1748094 baseEnd_1748094 := by
    simpa [prefixWord, tailWord_1748094, baseEnd_1748094] using wordTrace_append hprefix tailTrace_1748094
  have hstable : (prefixWord ++ tailWord_1748094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748094).length < 2 ^ (prefixWord ++ tailWord_1748094).sum := by decide
  have hdescent : baseEnd_1748094 < baseStart_1748094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748099 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 2, 4]
def baseStart_1748099 : Nat := 118140960795 + 1748099 * 2 ^ 59
def prefixEnd_1748099 : Nat := 4983230072969 + 3 ^ 40 * 1748099 * 2
def baseEnd_1748099 : Nat := 299205006214687096107715

theorem tailTrace_1748099 : CollatzResearch.WordTrace tailWord_1748099 prefixEnd_1748099 299205006214687096107715 := by
  unfold tailWord_1748099
  simp only [CollatzResearch.WordTrace]
  refine ⟨63758408493943349385407351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42505605662628899590271567 63758408493943349385407351)
  ·
    refine ⟨95637612740915024078111027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63758408493943349385407351 95637612740915024078111027)
    ·
      refine ⟨143456419111372536117166541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95637612740915024078111027 143456419111372536117166541)
      ·
        refine ⟨53796157166764701043937453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143456419111372536117166541 53796157166764701043937453)
        ·
          refine ⟨20173558937536762891476545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53796157166764701043937453 20173558937536762891476545)
          ·
            refine ⟨15130169203152572168607409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20173558937536762891476545 15130169203152572168607409)
            ·
              refine ⟨11347626902364429126455557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15130169203152572168607409 11347626902364429126455557)
              ·
                refine ⟨2127680044193330461210417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11347626902364429126455557 2127680044193330461210417)
                ·
                  refine ⟨1595760033144997845907813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127680044193330461210417 1595760033144997845907813)
                  ·
                    refine ⟨299205006214687096107715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595760033144997845907813 299205006214687096107715)
                    ·
                      rfl

theorem cell23_1748099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 4].length) (baseStart_1748099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748099 prefixEnd_1748099 := by exact prefixLift 1748099
  have htrace : WordTrace (prefixWord ++ tailWord_1748099) baseStart_1748099 baseEnd_1748099 := by
    simpa [prefixWord, tailWord_1748099, baseEnd_1748099] using wordTrace_append hprefix tailTrace_1748099
  have hstable : (prefixWord ++ tailWord_1748099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748099).length < 2 ^ (prefixWord ++ tailWord_1748099).sum := by decide
  have hdescent : baseEnd_1748099 < baseStart_1748099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748100 : List Nat := [2, 3, 2, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_1748100 : Nat := 118140960795 + 1748100 * 2 ^ 59
def prefixEnd_1748100 : Nat := 4983230072969 + 3 ^ 40 * 1748100 * 2
def baseEnd_1748100 : Nat := 897615532124715784410641

theorem tailTrace_1748100 : CollatzResearch.WordTrace tailWord_1748100 prefixEnd_1748100 897615532124715784410641 := by
  unfold tailWord_1748100
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879222483469863278096877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42505629977959817704129169 31879222483469863278096877)
  ·
    refine ⟨11954708431301198729286329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31879222483469863278096877 11954708431301198729286329)
    ·
      refine ⟨8966031323475899046964747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11954708431301198729286329 8966031323475899046964747)
      ·
        refine ⟨13449046985213848570447121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8966031323475899046964747 13449046985213848570447121)
        ·
          refine ⟨10086785238910386427835341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13449046985213848570447121 10086785238910386427835341)
          ·
            refine ⟨3782544464591394910438253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10086785238910386427835341 3782544464591394910438253)
            ·
              refine ⟨1418454174221773091414345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3782544464591394910438253 1418454174221773091414345)
              ·
                refine ⟨1063840630666329818560759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418454174221773091414345 1063840630666329818560759)
                ·
                  refine ⟨1595760945999494727841139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063840630666329818560759 1595760945999494727841139)
                  ·
                    refine ⟨2393641418999242091761709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1595760945999494727841139 2393641418999242091761709)
                    ·
                      refine ⟨897615532124715784410641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2393641418999242091761709 897615532124715784410641)
                      ·
                        rfl

theorem cell23_1748100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_1748100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748100 prefixEnd_1748100 := by exact prefixLift 1748100
  have htrace : WordTrace (prefixWord ++ tailWord_1748100) baseStart_1748100 baseEnd_1748100 := by
    simpa [prefixWord, tailWord_1748100, baseEnd_1748100] using wordTrace_append hprefix tailTrace_1748100
  have hstable : (prefixWord ++ tailWord_1748100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748100).length < 2 ^ (prefixWord ++ tailWord_1748100).sum := by decide
  have hdescent : baseEnd_1748100 < baseStart_1748100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748179 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 5, 4, 2]
def baseStart_1748179 : Nat := 118140960795 + 1748179 * 2 ^ 59
def prefixEnd_1748179 : Nat := 4983230072969 + 3 ^ 40 * 1748179 * 2
def baseEnd_1748179 : Nat := 897656097096420975322777

theorem tailTrace_1748179 : CollatzResearch.WordTrace tailWord_1748179 prefixEnd_1748179 897656097096420975322777 := by
  unfold tailWord_1748179
  simp only [CollatzResearch.WordTrace]
  refine ⟨63761326333653523048319591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42507550889102348698879727 63761326333653523048319591)
  ·
    refine ⟨95641989500480284572479387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63761326333653523048319591 95641989500480284572479387)
    ·
      refine ⟨143462984250720426858719081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95641989500480284572479387 143462984250720426858719081)
      ·
        refine ⟨107597238188040320144039311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143462984250720426858719081 107597238188040320144039311)
        ·
          refine ⟨161395857282060480216058967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107597238188040320144039311 161395857282060480216058967)
          ·
            refine ⟨242093785923090720324088451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161395857282060480216058967 242093785923090720324088451)
            ·
              refine ⟨363140678884636080486132677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242093785923090720324088451 363140678884636080486132677)
              ·
                refine ⟨68088877290869265091149877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363140678884636080486132677 68088877290869265091149877)
                ·
                  refine ⟨6383332246018993602295301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68088877290869265091149877 6383332246018993602295301)
                  ·
                    refine ⟨1196874796128561300430369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6383332246018993602295301 1196874796128561300430369)
                    ·
                      refine ⟨897656097096420975322777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196874796128561300430369 897656097096420975322777)
                      ·
                        rfl

theorem cell23_1748179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4, 2].length) (baseStart_1748179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748179 prefixEnd_1748179 := by exact prefixLift 1748179
  have htrace : WordTrace (prefixWord ++ tailWord_1748179) baseStart_1748179 baseEnd_1748179 := by
    simpa [prefixWord, tailWord_1748179, baseEnd_1748179] using wordTrace_append hprefix tailTrace_1748179
  have hstable : (prefixWord ++ tailWord_1748179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748179).length < 2 ^ (prefixWord ++ tailWord_1748179).sum := by decide
  have hdescent : baseEnd_1748179 < baseStart_1748179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748196 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_1748196 : Nat := 118140960795 + 1748196 * 2 ^ 59
def prefixEnd_1748196 : Nat := 4983230072969 + 3 ^ 40 * 1748196 * 2
def baseEnd_1748196 : Nat := 897664826267547408810199

theorem tailTrace_1748196 : CollatzResearch.WordTrace tailWord_1748196 prefixEnd_1748196 897664826267547408810199 := by
  unfold tailWord_1748196
  simp only [CollatzResearch.WordTrace]
  refine ⟨31880973187295967475844221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42507964249727956634458961 31880973187295967475844221)
  ·
    refine ⟨11955364945235987803441583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31880973187295967475844221 11955364945235987803441583)
    ·
      refine ⟨17933047417853981705162375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11955364945235987803441583 17933047417853981705162375)
      ·
        refine ⟨26899571126780972557743563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17933047417853981705162375 26899571126780972557743563)
        ·
          refine ⟨40349356690171458836615345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26899571126780972557743563 40349356690171458836615345)
          ·
            refine ⟨30262017517628594127461509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40349356690171458836615345 30262017517628594127461509)
            ·
              refine ⟨5674128284555361398899033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30262017517628594127461509 5674128284555361398899033)
              ·
                refine ⟨4255596213416521049174275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674128284555361398899033 4255596213416521049174275)
                ·
                  refine ⟨6383394320124781573761413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255596213416521049174275 6383394320124781573761413)
                  ·
                    refine ⟨1196886435023396545080265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6383394320124781573761413 1196886435023396545080265)
                    ·
                      refine ⟨897664826267547408810199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196886435023396545080265 897664826267547408810199)
                      ·
                        rfl

theorem cell23_1748196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_1748196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748196 prefixEnd_1748196 := by exact prefixLift 1748196
  have htrace : WordTrace (prefixWord ++ tailWord_1748196) baseStart_1748196 baseEnd_1748196 := by
    simpa [prefixWord, tailWord_1748196, baseEnd_1748196] using wordTrace_append hprefix tailTrace_1748196
  have hstable : (prefixWord ++ tailWord_1748196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748196).length < 2 ^ (prefixWord ++ tailWord_1748196).sum := by decide
  have hdescent : baseEnd_1748196 < baseStart_1748196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748229 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_1748229 : Nat := 118140960795 + 1748229 * 2 ^ 59
def prefixEnd_1748229 : Nat := 4983230072969 + 3 ^ 40 * 1748229 * 2
def baseEnd_1748229 : Nat := 897681771129145779697547

theorem tailTrace_1748229 : CollatzResearch.WordTrace tailWord_1748229 prefixEnd_1748229 897681771129145779697547 := by
  unfold tailWord_1748229
  simp only [CollatzResearch.WordTrace]
  refine ⟨63763149983472381587639741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42508766655648254391759827 63763149983472381587639741)
  ·
    refine ⟨23911181243802143095364903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63763149983472381587639741 23911181243802143095364903)
    ·
      refine ⟨35866771865703214643047355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23911181243802143095364903 35866771865703214643047355)
      ·
        refine ⟨53800157798554821964571033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35866771865703214643047355 53800157798554821964571033)
        ·
          refine ⟨40350118348916116473428275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53800157798554821964571033 40350118348916116473428275)
          ·
            refine ⟨60525177523374174710142413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40350118348916116473428275 60525177523374174710142413)
            ·
              refine ⟨22696941571265315516303405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60525177523374174710142413 22696941571265315516303405)
              ·
                refine ⟨8511353089224493318613777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22696941571265315516303405 8511353089224493318613777)
                ·
                  refine ⟨6383514816918369988960333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8511353089224493318613777 6383514816918369988960333)
                  ·
                    refine ⟨2393818056344388745860125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6383514816918369988960333 2393818056344388745860125)
                    ·
                      refine ⟨897681771129145779697547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2393818056344388745860125 897681771129145779697547)
                      ·
                        rfl

theorem cell23_1748229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_1748229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748229 prefixEnd_1748229 := by exact prefixLift 1748229
  have htrace : WordTrace (prefixWord ++ tailWord_1748229) baseStart_1748229 baseEnd_1748229 := by
    simpa [prefixWord, tailWord_1748229, baseEnd_1748229] using wordTrace_append hprefix tailTrace_1748229
  have hstable : (prefixWord ++ tailWord_1748229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748229).length < 2 ^ (prefixWord ++ tailWord_1748229).sum := by decide
  have hdescent : baseEnd_1748229 < baseStart_1748229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748253 : List Nat := [1, 4, 2, 3, 1, 1, 3, 3, 5]
def baseStart_1748253 : Nat := 118140960795 + 1748253 * 2 ^ 59
def prefixEnd_1748253 : Nat := 4983230072969 + 3 ^ 40 * 1748253 * 2
def baseEnd_1748253 : Nat := 99743788296094853977493

theorem tailTrace_1748253 : CollatzResearch.WordTrace tailWord_1748253 prefixEnd_1748253 99743788296094853977493 := by
  unfold tailWord_1748253
  simp only [CollatzResearch.WordTrace]
  refine ⟨63764025335385433686513413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42509350223590289124342275 63764025335385433686513413)
  ·
    refine ⟨11955754750384768816221265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63764025335385433686513413 11955754750384768816221265)
    ·
      refine ⟨8966816062788576612165949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11955754750384768816221265 8966816062788576612165949)
      ·
        refine ⟨3362556023545716229562231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8966816062788576612165949 3362556023545716229562231)
        ·
          refine ⟨5043834035318574344343347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362556023545716229562231 5043834035318574344343347)
          ·
            refine ⟨7565751052977861516515021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043834035318574344343347 7565751052977861516515021)
            ·
              refine ⟨2837156644866698068693133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7565751052977861516515021 2837156644866698068693133)
              ·
                refine ⟨1063933741825011775759925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2837156644866698068693133 1063933741825011775759925)
                ·
                  refine ⟨99743788296094853977493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1063933741825011775759925 99743788296094853977493)
                  ·
                    rfl

theorem cell23_1748253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_1748253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748253 prefixEnd_1748253 := by exact prefixLift 1748253
  have htrace : WordTrace (prefixWord ++ tailWord_1748253) baseStart_1748253 baseEnd_1748253 := by
    simpa [prefixWord, tailWord_1748253, baseEnd_1748253] using wordTrace_append hprefix tailTrace_1748253
  have hstable : (prefixWord ++ tailWord_1748253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748253).length < 2 ^ (prefixWord ++ tailWord_1748253).sum := by decide
  have hdescent : baseEnd_1748253 < baseStart_1748253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748266 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1748266 : Nat := 118140960795 + 1748266 * 2 ^ 59
def prefixEnd_1748266 : Nat := 4983230072969 + 3 ^ 40 * 1748266 * 2
def baseEnd_1748266 : Nat := 299233589971120711644959

theorem tailTrace_1748266 : CollatzResearch.WordTrace tailWord_1748266 prefixEnd_1748266 299233589971120711644959 := by
  unfold tailWord_1748266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15941124871084584226684163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42509666322892224604491101 15941124871084584226684163)
  ·
    refine ⟨23911687306626876340026245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15941124871084584226684163 23911687306626876340026245)
    ·
      refine ⟨4483441369992539313754921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23911687306626876340026245 4483441369992539313754921)
      ·
        refine ⟨3362581027494404485316191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4483441369992539313754921 3362581027494404485316191)
        ·
          refine ⟨5043871541241606727974287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362581027494404485316191 5043871541241606727974287)
          ·
            refine ⟨7565807311862410091961431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043871541241606727974287 7565807311862410091961431)
            ·
              refine ⟨11348710967793615137942147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7565807311862410091961431 11348710967793615137942147)
              ·
                refine ⟨17023066451690422706913221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11348710967793615137942147 17023066451690422706913221)
                ·
                  refine ⟨3191824959691954257546229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17023066451690422706913221 3191824959691954257546229)
                  ·
                    refine ⟨299233589971120711644959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3191824959691954257546229 299233589971120711644959)
                    ·
                      rfl

theorem cell23_1748266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1748266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748266 prefixEnd_1748266 := by exact prefixLift 1748266
  have htrace : WordTrace (prefixWord ++ tailWord_1748266) baseStart_1748266 baseEnd_1748266 := by
    simpa [prefixWord, tailWord_1748266, baseEnd_1748266] using wordTrace_append hprefix tailTrace_1748266
  have hstable : (prefixWord ++ tailWord_1748266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748266).length < 2 ^ (prefixWord ++ tailWord_1748266).sum := by decide
  have hdescent : baseEnd_1748266 < baseStart_1748266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748276 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1748276 : Nat := 118140960795 + 1748276 * 2 ^ 59
def prefixEnd_1748276 : Nat := 4983230072969 + 3 ^ 40 * 1748276 * 2
def baseEnd_1748276 : Nat := 897705904719907095809831

theorem tailTrace_1748276 : CollatzResearch.WordTrace tailWord_1748276 prefixEnd_1748276 897705904719907095809831 := by
  unfold tailWord_1748276
  simp only [CollatzResearch.WordTrace]
  refine ⟨31882432107151054307300341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42509909476201405743067121 31882432107151054307300341)
  ·
    refine ⟨2988978010045411341309407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31882432107151054307300341 2988978010045411341309407)
    ·
      refine ⟨4483467015068117011964111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988978010045411341309407 4483467015068117011964111)
      ·
        refine ⟨6725200522602175517946167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483467015068117011964111 6725200522602175517946167)
        ·
          refine ⟨10087800783903263276919251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725200522602175517946167 10087800783903263276919251)
          ·
            refine ⟨15131701175854894915378877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10087800783903263276919251 15131701175854894915378877)
            ·
              refine ⟨5674387940945585593267079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15131701175854894915378877 5674387940945585593267079)
              ·
                refine ⟨8511581911418378389900619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674387940945585593267079 8511581911418378389900619)
                ·
                  refine ⟨12767372867127567584850929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8511581911418378389900619 12767372867127567584850929)
                  ·
                    refine ⟨9575529650345675688638197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12767372867127567584850929 9575529650345675688638197)
                    ·
                      refine ⟨897705904719907095809831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9575529650345675688638197 897705904719907095809831)
                      ·
                        rfl

theorem cell23_1748276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1748276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748276 prefixEnd_1748276 := by exact prefixLift 1748276
  have htrace : WordTrace (prefixWord ++ tailWord_1748276) baseStart_1748276 baseEnd_1748276 := by
    simpa [prefixWord, tailWord_1748276, baseEnd_1748276] using wordTrace_append hprefix tailTrace_1748276
  have hstable : (prefixWord ++ tailWord_1748276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748276).length < 2 ^ (prefixWord ++ tailWord_1748276).sum := by decide
  have hdescent : baseEnd_1748276 < baseStart_1748276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748286 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1748286 : Nat := 118140960795 + 1748286 * 2 ^ 59
def prefixEnd_1748286 : Nat := 4983230072969 + 3 ^ 40 * 1748286 * 2
def baseEnd_1748286 : Nat := 897711039526452056684785

theorem tailTrace_1748286 : CollatzResearch.WordTrace tailWord_1748286 prefixEnd_1748286 897711039526452056684785 := by
  unfold tailWord_1748286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7970653618033235040308089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42510152629510586881643141 7970653618033235040308089)
  ·
    refine ⟨5977990213524926280231067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7970653618033235040308089 5977990213524926280231067)
    ·
      refine ⟨8966985320287389420346601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5977990213524926280231067 8966985320287389420346601)
      ·
        refine ⟨6725238990215542065259951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8966985320287389420346601 6725238990215542065259951)
        ·
          refine ⟨10087858485323313097889927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725238990215542065259951 10087858485323313097889927)
          ·
            refine ⟨15131787727984969646834891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10087858485323313097889927 15131787727984969646834891)
            ·
              refine ⟨22697681591977454470252337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15131787727984969646834891 22697681591977454470252337)
              ·
                refine ⟨17023261193983090852689253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22697681591977454470252337 17023261193983090852689253)
                ·
                  refine ⟨3191861473871829534879235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17023261193983090852689253 3191861473871829534879235)
                  ·
                    refine ⟨4787792210807744302318853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3191861473871829534879235 4787792210807744302318853)
                    ·
                      refine ⟨897711039526452056684785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4787792210807744302318853 897711039526452056684785)
                      ·
                        rfl

theorem cell23_1748286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1748286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748286 prefixEnd_1748286 := by exact prefixLift 1748286
  have htrace : WordTrace (prefixWord ++ tailWord_1748286) baseStart_1748286 baseEnd_1748286 := by
    simpa [prefixWord, tailWord_1748286, baseEnd_1748286] using wordTrace_append hprefix tailTrace_1748286
  have hstable : (prefixWord ++ tailWord_1748286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748286).length < 2 ^ (prefixWord ++ tailWord_1748286).sum := by decide
  have hdescent : baseEnd_1748286 < baseStart_1748286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748346 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2]
def baseStart_1748346 : Nat := 118140960795 + 1748346 * 2 ^ 59
def prefixEnd_1748346 : Nat := 4983230072969 + 3 ^ 40 * 1748346 * 2
def baseEnd_1748346 : Nat := 897741848365721821934509

theorem tailTrace_1748346 : CollatzResearch.WordTrace tailWord_1748346 prefixEnd_1748346 897741848365721821934509 := by
  unfold tailWord_1748346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15941854331012127642412223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42511611549365673713099261 15941854331012127642412223)
  ·
    refine ⟨23912781496518191463618335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15941854331012127642412223 23912781496518191463618335)
    ·
      refine ⟨35869172244777287195427503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23912781496518191463618335 35869172244777287195427503)
      ·
        refine ⟨53803758367165930793141255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35869172244777287195427503 53803758367165930793141255)
        ·
          refine ⟨80705637550748896189711883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53803758367165930793141255 80705637550748896189711883)
          ·
            refine ⟨121058456326123344284567825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80705637550748896189711883 121058456326123344284567825)
            ·
              refine ⟨90793842244592508213425869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121058456326123344284567825 90793842244592508213425869)
              ·
                refine ⟨34047690841722190580034701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90793842244592508213425869 34047690841722190580034701)
                ·
                  refine ⟨12767884065645821467513013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34047690841722190580034701 12767884065645821467513013)
                  ·
                    refine ⟨1196989131154295762579345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12767884065645821467513013 1196989131154295762579345)
                    ·
                      refine ⟨897741848365721821934509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1196989131154295762579345 897741848365721821934509)
                      ·
                        rfl

theorem cell23_1748346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_1748346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748346 prefixEnd_1748346 := by exact prefixLift 1748346
  have htrace : WordTrace (prefixWord ++ tailWord_1748346) baseStart_1748346 baseEnd_1748346 := by
    simpa [prefixWord, tailWord_1748346, baseEnd_1748346] using wordTrace_append hprefix tailTrace_1748346
  have hstable : (prefixWord ++ tailWord_1748346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748346).length < 2 ^ (prefixWord ++ tailWord_1748346).sum := by decide
  have hdescent : baseEnd_1748346 < baseStart_1748346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748349 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1748349 : Nat := 118140960795 + 1748349 * 2 ^ 59
def prefixEnd_1748349 : Nat := 4983230072969 + 3 ^ 40 * 1748349 * 2
def baseEnd_1748349 : Nat := 897743388807685310196995

theorem tailTrace_1748349 : CollatzResearch.WordTrace tailWord_1748349 prefixEnd_1748349 897743388807685310196995 := by
  unfold tailWord_1748349
  simp only [CollatzResearch.WordTrace]
  refine ⟨63767526743037642082008101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42511684495358428054672067 63767526743037642082008101)
  ·
    refine ⟨11956411264319557890376519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63767526743037642082008101 11956411264319557890376519)
    ·
      refine ⟨17934616896479336835564779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11956411264319557890376519 17934616896479336835564779)
      ·
        refine ⟨26901925344719005253347169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17934616896479336835564779 26901925344719005253347169)
        ·
          refine ⟨20176444008539253940010377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26901925344719005253347169 20176444008539253940010377)
          ·
            refine ⟨15132333006404440455007783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20176444008539253940010377 15132333006404440455007783)
            ·
              refine ⟨22698499509606660682511675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15132333006404440455007783 22698499509606660682511675)
              ·
                refine ⟨34047749264409991023767513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22698499509606660682511675 34047749264409991023767513)
                ·
                  refine ⟨25535811948307493267825635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34047749264409991023767513 25535811948307493267825635)
                  ·
                    refine ⟨38303717922461239901738453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25535811948307493267825635 38303717922461239901738453)
                    ·
                      refine ⟨897743388807685310196995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38303717922461239901738453 897743388807685310196995)
                      ·
                        rfl

theorem cell23_1748349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1748349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748349 prefixEnd_1748349 := by exact prefixLift 1748349
  have htrace : WordTrace (prefixWord ++ tailWord_1748349) baseStart_1748349 baseEnd_1748349 := by
    simpa [prefixWord, tailWord_1748349, baseEnd_1748349] using wordTrace_append hprefix tailTrace_1748349
  have hstable : (prefixWord ++ tailWord_1748349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748349).length < 2 ^ (prefixWord ++ tailWord_1748349).sum := by decide
  have hdescent : baseEnd_1748349 < baseStart_1748349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748356 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1748356 : Nat := 118140960795 + 1748356 * 2 ^ 59
def prefixEnd_1748356 : Nat := 4983230072969 + 3 ^ 40 * 1748356 * 2
def baseEnd_1748356 : Nat := 299248994390755594269821

theorem tailTrace_1748356 : CollatzResearch.WordTrace tailWord_1748356 prefixEnd_1748356 299248994390755594269821 := by
  unfold tailWord_1748356
  simp only [CollatzResearch.WordTrace]
  refine ⟨31883891027006141138756461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42511854702674854851675281 31883891027006141138756461)
  ·
    refine ⟨11956459135127302927033673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31883891027006141138756461 11956459135127302927033673)
    ·
      refine ⟨8967344351345477195275255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11956459135127302927033673 8967344351345477195275255)
      ·
        refine ⟨13451016527018215792912883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8967344351345477195275255 13451016527018215792912883)
        ·
          refine ⟨20176524790527323689369325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13451016527018215792912883 20176524790527323689369325)
          ·
            refine ⟨7566196796447746383513497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20176524790527323689369325 7566196796447746383513497)
            ·
              refine ⟨5674647597335809787635123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7566196796447746383513497 5674647597335809787635123)
              ·
                refine ⟨8511971396003714681452685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674647597335809787635123 8511971396003714681452685)
                ·
                  refine ⟨3191989273501393005544757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8511971396003714681452685 3191989273501393005544757)
                  ·
                    refine ⟨299248994390755594269821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3191989273501393005544757 299248994390755594269821)
                    ·
                      rfl

theorem cell23_1748356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1748356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748356 prefixEnd_1748356 := by exact prefixLift 1748356
  have htrace : WordTrace (prefixWord ++ tailWord_1748356) baseStart_1748356 baseEnd_1748356 := by
    simpa [prefixWord, tailWord_1748356, baseEnd_1748356] using wordTrace_append hprefix tailTrace_1748356
  have hstable : (prefixWord ++ tailWord_1748356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748356).length < 2 ^ (prefixWord ++ tailWord_1748356).sum := by decide
  have hdescent : baseEnd_1748356 < baseStart_1748356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748373 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_1748373 : Nat := 118140960795 + 1748373 * 2 ^ 59
def prefixEnd_1748373 : Nat := 4983230072969 + 3 ^ 40 * 1748373 * 2
def baseEnd_1748373 : Nat := 299251904114464405432295

theorem tailTrace_1748373 : CollatzResearch.WordTrace tailWord_1748373 prefixEnd_1748373 299251904114464405432295 := by
  unfold tailWord_1748373
  simp only [CollatzResearch.WordTrace]
  refine ⟨63768402094950694180881773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42512268063300462787254515 63768402094950694180881773)
  ·
    refine ⟨23913150785606510317830665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63768402094950694180881773 23913150785606510317830665)
    ·
      refine ⟨17934863089204882738372999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23913150785606510317830665 17934863089204882738372999)
      ·
        refine ⟨26902294633807324107559499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17934863089204882738372999 26902294633807324107559499)
        ·
          refine ⟨40353441950710986161339249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26902294633807324107559499 40353441950710986161339249)
          ·
            refine ⟨30265081463033239621004437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40353441950710986161339249 30265081463033239621004437)
            ·
              refine ⟨1418675693579683107234583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30265081463033239621004437 1418675693579683107234583)
              ·
                refine ⟨2128013540369524660851875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418675693579683107234583 2128013540369524660851875)
                ·
                  refine ⟨3192020310554286991277813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128013540369524660851875 3192020310554286991277813)
                  ·
                    refine ⟨299251904114464405432295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3192020310554286991277813 299251904114464405432295)
                    ·
                      rfl

theorem cell23_1748373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_1748373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748373 prefixEnd_1748373 := by exact prefixLift 1748373
  have htrace : WordTrace (prefixWord ++ tailWord_1748373) baseStart_1748373 baseEnd_1748373 := by
    simpa [prefixWord, tailWord_1748373, baseEnd_1748373] using wordTrace_append hprefix tailTrace_1748373
  have hstable : (prefixWord ++ tailWord_1748373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748373).length < 2 ^ (prefixWord ++ tailWord_1748373).sum := by decide
  have hdescent : baseEnd_1748373 < baseStart_1748373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748396 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_1748396 : Nat := 118140960795 + 1748396 * 2 ^ 59
def prefixEnd_1748396 : Nat := 4983230072969 + 3 ^ 40 * 1748396 * 2
def baseEnd_1748396 : Nat := 897767522398446626309279

theorem tailTrace_1748396 : CollatzResearch.WordTrace tailWord_1748396 prefixEnd_1748396 897767522398446626309279 := by
  unfold tailWord_1748396
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884620486933684554484521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42512827315911579405979361 31884620486933684554484521)
  ·
    refine ⟨23913465365200263415863391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31884620486933684554484521 23913465365200263415863391)
    ·
      refine ⟨35870198047800395123795087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23913465365200263415863391 35870198047800395123795087)
      ·
        refine ⟨53805297071700592685692631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35870198047800395123795087 53805297071700592685692631)
        ·
          refine ⟨80707945607550889028538947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53805297071700592685692631 80707945607550889028538947)
          ·
            refine ⟨121061918411326333542808421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80707945607550889028538947 121061918411326333542808421)
            ·
              refine ⟨22699109702123687539276579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121061918411326333542808421 22699109702123687539276579)
              ·
                refine ⟨34048664553185531308914869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22699109702123687539276579 34048664553185531308914869)
                ·
                  refine ⟨3192062301861143560210769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34048664553185531308914869 3192062301861143560210769)
                  ·
                    refine ⟨2394046726395857670158077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3192062301861143560210769 2394046726395857670158077)
                    ·
                      refine ⟨897767522398446626309279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2394046726395857670158077 897767522398446626309279)
                      ·
                        rfl

theorem cell23_1748396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_1748396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748396 prefixEnd_1748396 := by exact prefixLift 1748396
  have htrace : WordTrace (prefixWord ++ tailWord_1748396) baseStart_1748396 baseEnd_1748396 := by
    simpa [prefixWord, tailWord_1748396, baseEnd_1748396] using wordTrace_append hprefix tailTrace_1748396
  have hstable : (prefixWord ++ tailWord_1748396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748396).length < 2 ^ (prefixWord ++ tailWord_1748396).sum := by decide
  have hdescent : baseEnd_1748396 < baseStart_1748396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748416 : List Nat := [2, 1, 1, 2, 3, 1, 6, 7]
def baseStart_1748416 : Nat := 118140960795 + 1748416 * 2 ^ 59
def prefixEnd_1748416 : Nat := 4983230072969 + 3 ^ 40 * 1748416 * 2
def baseEnd_1748416 : Nat := 33251029333760612891081

theorem tailTrace_1748416 : CollatzResearch.WordTrace tailWord_1748416 prefixEnd_1748416 33251029333760612891081 := by
  unfold tailWord_1748416
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884985216897456262348551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42513313622529941683131401 31884985216897456262348551)
  ·
    refine ⟨47827477825346184393522827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31884985216897456262348551 47827477825346184393522827)
    ·
      refine ⟨71741216738019276590284241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47827477825346184393522827 71741216738019276590284241)
      ·
        refine ⟨53805912553514457442713181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71741216738019276590284241 53805912553514457442713181)
        ·
          refine ⟨20177217207567921541017443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53805912553514457442713181 20177217207567921541017443)
          ·
            refine ⟨30265825811351882311526165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20177217207567921541017443 30265825811351882311526165)
            ·
              refine ⟨1418710584907119483352789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30265825811351882311526165 1418710584907119483352789)
              ·
                refine ⟨33251029333760612891081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1418710584907119483352789 33251029333760612891081)
                ·
                  rfl

theorem cell23_1748416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 7].length) (baseStart_1748416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748416 prefixEnd_1748416 := by exact prefixLift 1748416
  have htrace : WordTrace (prefixWord ++ tailWord_1748416) baseStart_1748416 baseEnd_1748416 := by
    simpa [prefixWord, tailWord_1748416, baseEnd_1748416] using wordTrace_append hprefix tailTrace_1748416
  have hstable : (prefixWord ++ tailWord_1748416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748416).length < 2 ^ (prefixWord ++ tailWord_1748416).sum := by decide
  have hdescent : baseEnd_1748416 < baseStart_1748416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748427 : List Nat := [1, 1, 1, 1, 3, 3, 5, 3, 1, 2, 2]
def baseStart_1748427 : Nat := 118140960795 + 1748427 * 2 ^ 59
def prefixEnd_1748427 : Nat := 4983230072969 + 3 ^ 40 * 1748427 * 2
def baseEnd_1748427 : Nat := 897783440298736005021637

theorem tailTrace_1748427 : CollatzResearch.WordTrace tailWord_1748427 prefixEnd_1748427 897783440298736005021637 := by
  unfold tailWord_1748427
  simp only [CollatzResearch.WordTrace]
  refine ⟨63770371636755061403347535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42513581091170040935565023 63770371636755061403347535)
  ·
    refine ⟨95655557455132592105021303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63770371636755061403347535 95655557455132592105021303)
    ·
      refine ⟨143483336182698888157531955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95655557455132592105021303 143483336182698888157531955)
      ·
        refine ⟨215225004274048332236297933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143483336182698888157531955 215225004274048332236297933)
        ·
          refine ⟨80709376602768124588611725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215225004274048332236297933 80709376602768124588611725)
          ·
            refine ⟨30266016226038046720729397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80709376602768124588611725 30266016226038046720729397)
            ·
              refine ⟨2837439021191066880068381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30266016226038046720729397 2837439021191066880068381)
              ·
                refine ⟨1064039632946650080025643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2837439021191066880068381 1064039632946650080025643)
                ·
                  refine ⟨1596059449419975120038465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064039632946650080025643 1596059449419975120038465)
                  ·
                    refine ⟨1197044587064981340028849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596059449419975120038465 1197044587064981340028849)
                    ·
                      refine ⟨897783440298736005021637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197044587064981340028849 897783440298736005021637)
                      ·
                        rfl

theorem cell23_1748427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 2, 2].length) (baseStart_1748427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748427 prefixEnd_1748427 := by exact prefixLift 1748427
  have htrace : WordTrace (prefixWord ++ tailWord_1748427) baseStart_1748427 baseEnd_1748427 := by
    simpa [prefixWord, tailWord_1748427, baseEnd_1748427] using wordTrace_append hprefix tailTrace_1748427
  have hstable : (prefixWord ++ tailWord_1748427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748427).length < 2 ^ (prefixWord ++ tailWord_1748427).sum := by decide
  have hdescent : baseEnd_1748427 < baseStart_1748427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748506 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 7]
def baseStart_1748506 : Nat := 118140960795 + 1748506 * 2 ^ 59
def prefixEnd_1748506 : Nat := 4983230072969 + 3 ^ 40 * 1748506 * 2
def baseEnd_1748506 : Nat := 99758222807826799548197

theorem tailTrace_1748506 : CollatzResearch.WordTrace tailWord_1748506 prefixEnd_1748506 99758222807826799548197 := by
  unfold tailWord_1748506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943313250867214473868343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42515502002312571930315581 15943313250867214473868343)
  ·
    refine ⟨23914969876300821710802515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15943313250867214473868343 23914969876300821710802515)
    ·
      refine ⟨35872454814451232566203773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23914969876300821710802515 35872454814451232566203773)
      ·
        refine ⟨13452170555419212212326415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35872454814451232566203773 13452170555419212212326415)
        ·
          refine ⟨20178255833128818318489623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13452170555419212212326415 20178255833128818318489623)
          ·
            refine ⟨30267383749693227477734435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20178255833128818318489623 30267383749693227477734435)
            ·
              refine ⟨45401075624539841216601653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30267383749693227477734435 45401075624539841216601653)
              ·
                refine ⟨4256350839800610114056405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45401075624539841216601653 4256350839800610114056405)
                ·
                  refine ⟨99758222807826799548197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4256350839800610114056405 99758222807826799548197)
                  ·
                    rfl

theorem cell23_1748506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_1748506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748506 prefixEnd_1748506 := by exact prefixLift 1748506
  have htrace : WordTrace (prefixWord ++ tailWord_1748506) baseStart_1748506 baseEnd_1748506 := by
    simpa [prefixWord, tailWord_1748506, baseEnd_1748506] using wordTrace_append hprefix tailTrace_1748506
  have hstable : (prefixWord ++ tailWord_1748506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748506).length < 2 ^ (prefixWord ++ tailWord_1748506).sum := by decide
  have hdescent : baseEnd_1748506 < baseStart_1748506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748513 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1748513 : Nat := 118140960795 + 1748513 * 2 ^ 59
def prefixEnd_1748513 : Nat := 4983230072969 + 3 ^ 40 * 1748513 * 2
def baseEnd_1748513 : Nat := 897827599635022668546241

theorem tailTrace_1748513 : CollatzResearch.WordTrace tailWord_1748513 prefixEnd_1748513 897827599635022668546241 := by
  unfold tailWord_1748513
  simp only [CollatzResearch.WordTrace]
  refine ⟨63773508314443498090978193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42515672209628998727318795 63773508314443498090978193)
  ·
    refine ⟨47830131235832623568233645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63773508314443498090978193 47830131235832623568233645)
    ·
      refine ⟨17936299213437233838087617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47830131235832623568233645 17936299213437233838087617)
      ·
        refine ⟨13452224410077925378565713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17936299213437233838087617 13452224410077925378565713)
        ·
          refine ⟨10089168307558444033924285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13452224410077925378565713 10089168307558444033924285)
          ·
            refine ⟨3783438115334416512721607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10089168307558444033924285 3783438115334416512721607)
            ·
              refine ⟨5675157173001624769082411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3783438115334416512721607 5675157173001624769082411)
              ·
                refine ⟨8512735759502437153623617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675157173001624769082411 8512735759502437153623617)
                ·
                  refine ⟨6384551819626827865217713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8512735759502437153623617 6384551819626827865217713)
                  ·
                    refine ⟨4788413864720120898913285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384551819626827865217713 4788413864720120898913285)
                    ·
                      refine ⟨897827599635022668546241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4788413864720120898913285 897827599635022668546241)
                      ·
                        rfl

theorem cell23_1748513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1748513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748513 prefixEnd_1748513 := by exact prefixLift 1748513
  have htrace : WordTrace (prefixWord ++ tailWord_1748513) baseStart_1748513 baseEnd_1748513 := by
    simpa [prefixWord, tailWord_1748513, baseEnd_1748513] using wordTrace_append hprefix tailTrace_1748513
  have hstable : (prefixWord ++ tailWord_1748513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748513).length < 2 ^ (prefixWord ++ tailWord_1748513).sum := by decide
  have hdescent : baseEnd_1748513 < baseStart_1748513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748551 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_1748551 : Nat := 118140960795 + 1748551 * 2 ^ 59
def prefixEnd_1748551 : Nat := 4983230072969 + 3 ^ 40 * 1748551 * 2
def baseEnd_1748551 : Nat := 897847111899893519871067

theorem tailTrace_1748551 : CollatzResearch.WordTrace tailWord_1748551 prefixEnd_1748551 897847111899893519871067 := by
  unfold tailWord_1748551
  simp only [CollatzResearch.WordTrace]
  refine ⟨63774894288305830580861507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42516596192203887053907671 63774894288305830580861507)
  ·
    refine ⟨95662341432458745871292261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63774894288305830580861507 95662341432458745871292261)
    ·
      refine ⟨17936689018586014850867299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95662341432458745871292261 17936689018586014850867299)
      ·
        refine ⟨26905033527879022276300949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17936689018586014850867299 26905033527879022276300949)
        ·
          refine ⟨1261173446619329169201607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26905033527879022276300949 1261173446619329169201607)
          ·
            refine ⟨1891760169928993753802411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261173446619329169201607 1891760169928993753802411)
            ·
              refine ⟨2837640254893490630703617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891760169928993753802411 2837640254893490630703617)
              ·
                refine ⟨2128230191170117973027713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837640254893490630703617 2128230191170117973027713)
                ·
                  refine ⟨1596172643377588479770785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2128230191170117973027713 1596172643377588479770785)
                  ·
                    refine ⟨1197129482533191359828089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596172643377588479770785 1197129482533191359828089)
                    ·
                      refine ⟨897847111899893519871067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197129482533191359828089 897847111899893519871067)
                      ·
                        rfl

theorem cell23_1748551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_1748551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748551 prefixEnd_1748551 := by exact prefixLift 1748551
  have htrace : WordTrace (prefixWord ++ tailWord_1748551) baseStart_1748551 baseEnd_1748551 := by
    simpa [prefixWord, tailWord_1748551, baseEnd_1748551] using wordTrace_append hprefix tailTrace_1748551
  have hstable : (prefixWord ++ tailWord_1748551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748551).length < 2 ^ (prefixWord ++ tailWord_1748551).sum := by decide
  have hdescent : baseEnd_1748551 < baseStart_1748551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748593 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_1748593 : Nat := 118140960795 + 1748593 * 2 ^ 59
def prefixEnd_1748593 : Nat := 4983230072969 + 3 ^ 40 * 1748593 * 2
def baseEnd_1748593 : Nat := 897868678087382355545873

theorem tailTrace_1748593 : CollatzResearch.WordTrace tailWord_1748593 prefixEnd_1748593 897868678087382355545873 := by
  unfold tailWord_1748593
  simp only [CollatzResearch.WordTrace]
  refine ⟨63776426154153671753890433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42517617436102447835926955 63776426154153671753890433)
  ·
    refine ⟨47832319615615253815417825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63776426154153671753890433 47832319615615253815417825)
    ·
      refine ⟨35874239711711440361563369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47832319615615253815417825 35874239711711440361563369)
      ·
        refine ⟨26905679783783580271172527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35874239711711440361563369 26905679783783580271172527)
        ·
          refine ⟨40358519675675370406758791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26905679783783580271172527 40358519675675370406758791)
          ·
            refine ⟨60537779513513055610138187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40358519675675370406758791 60537779513513055610138187)
            ·
              refine ⟨90806669270269583415207281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60537779513513055610138187 90806669270269583415207281)
              ·
                refine ⟨68105001952702187561405461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90806669270269583415207281 68105001952702187561405461)
                ·
                  refine ⟨3192421966532915041940881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68105001952702187561405461 3192421966532915041940881)
                  ·
                    refine ⟨2394316474899686281455661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3192421966532915041940881 2394316474899686281455661)
                    ·
                      refine ⟨897868678087382355545873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2394316474899686281455661 897868678087382355545873)
                      ·
                        rfl

theorem cell23_1748593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_1748593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748593 prefixEnd_1748593 := by exact prefixLift 1748593
  have htrace : WordTrace (prefixWord ++ tailWord_1748593) baseStart_1748593 baseEnd_1748593 := by
    simpa [prefixWord, tailWord_1748593, baseEnd_1748593] using wordTrace_append hprefix tailTrace_1748593
  have hstable : (prefixWord ++ tailWord_1748593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748593).length < 2 ^ (prefixWord ++ tailWord_1748593).sum := by decide
  have hdescent : baseEnd_1748593 < baseStart_1748593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748613 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 6]
def baseStart_1748613 : Nat := 118140960795 + 1748613 * 2 ^ 59
def prefixEnd_1748613 : Nat := 4983230072969 + 3 ^ 40 * 1748613 * 2
def baseEnd_1748613 : Nat := 99764327522274697477309

theorem tailTrace_1748613 : CollatzResearch.WordTrace tailWord_1748613 prefixEnd_1748613 99764327522274697477309 := by
  unfold tailWord_1748613
  simp only [CollatzResearch.WordTrace]
  refine ⟨63777155614081215169618493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42518103742720810113078995 63777155614081215169618493)
  ·
    refine ⟨23916433355280455688606935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63777155614081215169618493 23916433355280455688606935)
    ·
      refine ⟨35874650032920683532910403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23916433355280455688606935 35874650032920683532910403)
      ·
        refine ⟨53811975049381025299365605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35874650032920683532910403 53811975049381025299365605)
        ·
          refine ⟨10089745321758942243631051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53811975049381025299365605 10089745321758942243631051)
          ·
            refine ⟨15134617982638413365446577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089745321758942243631051 15134617982638413365446577)
            ·
              refine ⟨11350963486978810024084933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15134617982638413365446577 11350963486978810024084933)
              ·
                refine ⟨2128305653808526879515925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11350963486978810024084933 2128305653808526879515925)
                ·
                  refine ⟨99764327522274697477309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2128305653808526879515925 99764327522274697477309)
                  ·
                    rfl

theorem cell23_1748613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_1748613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748613 prefixEnd_1748613 := by exact prefixLift 1748613
  have htrace : WordTrace (prefixWord ++ tailWord_1748613) baseStart_1748613 baseEnd_1748613 := by
    simpa [prefixWord, tailWord_1748613, baseEnd_1748613] using wordTrace_append hprefix tailTrace_1748613
  have hstable : (prefixWord ++ tailWord_1748613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748613).length < 2 ^ (prefixWord ++ tailWord_1748613).sum := by decide
  have hdescent : baseEnd_1748613 < baseStart_1748613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748643 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 3, 5]
def baseStart_1748643 : Nat := 118140960795 + 1748643 * 2 ^ 59
def prefixEnd_1748643 : Nat := 4983230072969 + 3 ^ 40 * 1748643 * 2
def baseEnd_1748643 : Nat := 299298117373369053306881

theorem tailTrace_1748643 : CollatzResearch.WordTrace tailWord_1748643 prefixEnd_1748643 299298117373369053306881 := by
  unfold tailWord_1748643
  simp only [CollatzResearch.WordTrace]
  refine ⟨63778249803972530293210583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42518833202648353528807055 63778249803972530293210583)
  ·
    refine ⟨95667374705958795439815875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63778249803972530293210583 95667374705958795439815875)
    ·
      refine ⟨143501062058938193159723813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95667374705958795439815875 143501062058938193159723813)
      ·
        refine ⟨26906449136050911217448215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143501062058938193159723813 26906449136050911217448215)
        ·
          refine ⟨40359673704076366826172323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26906449136050911217448215 40359673704076366826172323)
          ·
            refine ⟨60539510556114550239258485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40359673704076366826172323 60539510556114550239258485)
            ·
              refine ⟨5675579114635739084930483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60539510556114550239258485 5675579114635739084930483)
              ·
                refine ⟨8513368671953608627395725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675579114635739084930483 8513368671953608627395725)
                ·
                  refine ⟨3192513251982603235273397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8513368671953608627395725 3192513251982603235273397)
                  ·
                    refine ⟨299298117373369053306881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3192513251982603235273397 299298117373369053306881)
                    ·
                      rfl

theorem cell23_1748643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 5].length) (baseStart_1748643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748643 prefixEnd_1748643 := by exact prefixLift 1748643
  have htrace : WordTrace (prefixWord ++ tailWord_1748643) baseStart_1748643 baseEnd_1748643 := by
    simpa [prefixWord, tailWord_1748643, baseEnd_1748643] using wordTrace_append hprefix tailTrace_1748643
  have hstable : (prefixWord ++ tailWord_1748643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748643).length < 2 ^ (prefixWord ++ tailWord_1748643).sum := by decide
  have hdescent : baseEnd_1748643 < baseStart_1748643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748683 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5]
def baseStart_1748683 : Nat := 118140960795 + 1748683 * 2 ^ 59
def prefixEnd_1748683 : Nat := 4983230072969 + 3 ^ 40 * 1748683 * 2
def baseEnd_1748683 : Nat := 897914891346287003420459

theorem tailTrace_1748683 : CollatzResearch.WordTrace tailWord_1748683 prefixEnd_1748683 897914891346287003420459 := by
  unfold tailWord_1748683
  simp only [CollatzResearch.WordTrace]
  refine ⟨63779708723827617124666703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42519805815885078083111135 63779708723827617124666703)
  ·
    refine ⟨95669563085741425687000055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63779708723827617124666703 95669563085741425687000055)
    ·
      refine ⟨143504344628612138530500083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95669563085741425687000055 143504344628612138530500083)
      ·
        refine ⟨215256516942918207795750125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143504344628612138530500083 215256516942918207795750125)
        ·
          refine ⟨80721193853594327923406297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215256516942918207795750125 80721193853594327923406297)
          ·
            refine ⟨60540895390195745942554723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80721193853594327923406297 60540895390195745942554723)
            ·
              refine ⟨90811343085293618913832085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60540895390195745942554723 90811343085293618913832085)
              ·
                refine ⟨4256781707123138386585879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90811343085293618913832085 4256781707123138386585879)
                ·
                  refine ⟨6385172560684707579878819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256781707123138386585879 6385172560684707579878819)
                  ·
                    refine ⟨9577758841027061369818229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6385172560684707579878819 9577758841027061369818229)
                    ·
                      refine ⟨897914891346287003420459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9577758841027061369818229 897914891346287003420459)
                      ·
                        rfl

theorem cell23_1748683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5].length) (baseStart_1748683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748683 prefixEnd_1748683 := by exact prefixLift 1748683
  have htrace : WordTrace (prefixWord ++ tailWord_1748683) baseStart_1748683 baseEnd_1748683 := by
    simpa [prefixWord, tailWord_1748683, baseEnd_1748683] using wordTrace_append hprefix tailTrace_1748683
  have hstable : (prefixWord ++ tailWord_1748683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748683).length < 2 ^ (prefixWord ++ tailWord_1748683).sum := by decide
  have hdescent : baseEnd_1748683 < baseStart_1748683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748690 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1748690 : Nat := 118140960795 + 1748690 * 2 ^ 59
def prefixEnd_1748690 : Nat := 4983230072969 + 3 ^ 40 * 1748690 * 2
def baseEnd_1748690 : Nat := 299306161903622825344309

theorem tailTrace_1748690 : CollatzResearch.WordTrace tailWord_1748690 prefixEnd_1748690 299306161903622825344309 := by
  unfold tailWord_1748690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15944991008700564330042881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42519976023201504880114349 15944991008700564330042881)
  ·
    refine ⟨11958743256525423247532161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15944991008700564330042881 11958743256525423247532161)
    ·
      refine ⟨8969057442394067435649121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11958743256525423247532161 8969057442394067435649121)
      ·
        refine ⟨6726793081795550576736841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8969057442394067435649121 6726793081795550576736841)
        ·
          refine ⟨5045094811346662932552631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6726793081795550576736841 5045094811346662932552631)
          ·
            refine ⟨7567642217019994398828947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045094811346662932552631 7567642217019994398828947)
            ·
              refine ⟨11351463325529991598243421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7567642217019994398828947 11351463325529991598243421)
              ·
                refine ⟨4256798747073746849341283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11351463325529991598243421 4256798747073746849341283)
                ·
                  refine ⟨6385198120610620274011925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256798747073746849341283 6385198120610620274011925)
                  ·
                    refine ⟨299306161903622825344309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6385198120610620274011925 299306161903622825344309)
                    ·
                      rfl

theorem cell23_1748690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1748690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748690 prefixEnd_1748690 := by exact prefixLift 1748690
  have htrace : WordTrace (prefixWord ++ tailWord_1748690) baseStart_1748690 baseEnd_1748690 := by
    simpa [prefixWord, tailWord_1748690, baseEnd_1748690] using wordTrace_append hprefix tailTrace_1748690
  have hstable : (prefixWord ++ tailWord_1748690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748690).length < 2 ^ (prefixWord ++ tailWord_1748690).sum := by decide
  have hdescent : baseEnd_1748690 < baseStart_1748690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748697 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 5, 2, 2]
def baseStart_1748697 : Nat := 118140960795 + 1748697 * 2 ^ 59
def prefixEnd_1748697 : Nat := 4983230072969 + 3 ^ 40 * 1748697 * 2
def baseEnd_1748697 : Nat := 897922080075449948645395

theorem tailTrace_1748697 : CollatzResearch.WordTrace tailWord_1748697 prefixEnd_1748697 897922080075449948645395 := by
  unfold tailWord_1748697
  simp only [CollatzResearch.WordTrace]
  refine ⟨63780219345776897515676345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42520146230517931677117563 63780219345776897515676345)
  ·
    refine ⟨47835164509332673136757259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63780219345776897515676345 47835164509332673136757259)
    ·
      refine ⟨71752746763999009705135889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47835164509332673136757259 71752746763999009705135889)
      ·
        refine ⟨53814560072999257278851917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71752746763999009705135889 53814560072999257278851917)
        ·
          refine ⟨20180460027374721479569469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53814560072999257278851917 20180460027374721479569469)
          ·
            refine ⟨7567672510265520554838551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20180460027374721479569469 7567672510265520554838551)
            ·
              refine ⟨11351508765398280832257827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7567672510265520554838551 11351508765398280832257827)
              ·
                refine ⟨17027263148097421248386741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11351508765398280832257827 17027263148097421248386741)
                ·
                  refine ⟨1596305920134133242036257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17027263148097421248386741 1596305920134133242036257)
                  ·
                    refine ⟨1197229440100599931527193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596305920134133242036257 1197229440100599931527193)
                    ·
                      refine ⟨897922080075449948645395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197229440100599931527193 897922080075449948645395)
                      ·
                        rfl

theorem cell23_1748697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_1748697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748697 prefixEnd_1748697 := by exact prefixLift 1748697
  have htrace : WordTrace (prefixWord ++ tailWord_1748697) baseStart_1748697 baseEnd_1748697 := by
    simpa [prefixWord, tailWord_1748697, baseEnd_1748697] using wordTrace_append hprefix tailTrace_1748697
  have hstable : (prefixWord ++ tailWord_1748697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748697).length < 2 ^ (prefixWord ++ tailWord_1748697).sum := by decide
  have hdescent : baseEnd_1748697 < baseStart_1748697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748711 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 1, 5]
def baseStart_1748711 : Nat := 118140960795 + 1748711 * 2 ^ 59
def prefixEnd_1748711 : Nat := 4983230072969 + 3 ^ 40 * 1748711 * 2
def baseEnd_1748711 : Nat := 299309756268204297956777

theorem tailTrace_1748711 : CollatzResearch.WordTrace tailWord_1748711 prefixEnd_1748711 299309756268204297956777 := by
  unfold tailWord_1748711
  simp only [CollatzResearch.WordTrace]
  refine ⟨63780729967726177906685987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42520486645150785271123991 63780729967726177906685987)
  ·
    refine ⟨95671094951589266860028981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63780729967726177906685987 95671094951589266860028981)
    ·
      refine ⟨8969165151711493768127717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95671094951589266860028981 8969165151711493768127717)
      ·
        refine ⟨1681718465945905081523947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8969165151711493768127717 1681718465945905081523947)
        ·
          refine ⟨2522577698918857622285921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681718465945905081523947 2522577698918857622285921)
          ·
            refine ⟨1891933274189143216714441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2522577698918857622285921 1891933274189143216714441)
            ·
              refine ⟨1418949955641857412535831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891933274189143216714441 1418949955641857412535831)
              ·
                refine ⟨2128424933462786118803747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418949955641857412535831 2128424933462786118803747)
                ·
                  refine ⟨3192637400194179178205621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128424933462786118803747 3192637400194179178205621)
                  ·
                    refine ⟨299309756268204297956777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3192637400194179178205621 299309756268204297956777)
                    ·
                      rfl

theorem cell23_1748711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_1748711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748711 prefixEnd_1748711 := by exact prefixLift 1748711
  have htrace : WordTrace (prefixWord ++ tailWord_1748711) baseStart_1748711 baseEnd_1748711 := by
    simpa [prefixWord, tailWord_1748711, baseEnd_1748711] using wordTrace_append hprefix tailTrace_1748711
  have hstable : (prefixWord ++ tailWord_1748711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748711).length < 2 ^ (prefixWord ++ tailWord_1748711).sum := by decide
  have hdescent : baseEnd_1748711 < baseStart_1748711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748733 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1748733 : Nat := 118140960795 + 1748733 * 2 ^ 59
def prefixEnd_1748733 : Nat := 4983230072969 + 3 ^ 40 * 1748733 * 2
def baseEnd_1748733 : Nat := 299313521793003935931743

theorem tailTrace_1748733 : CollatzResearch.WordTrace tailWord_1748733 prefixEnd_1748733 299313521793003935931743 := by
  unfold tailWord_1748733
  simp only [CollatzResearch.WordTrace]
  refine ⟨63781532373646475663986853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42521021582430983775991235 63781532373646475663986853)
  ·
    refine ⟨11959037320058714186997535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63781532373646475663986853 11959037320058714186997535)
    ·
      refine ⟨17938555980088071280496303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11959037320058714186997535 17938555980088071280496303)
      ·
        refine ⟨26907833970132106920744455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17938555980088071280496303 26907833970132106920744455)
        ·
          refine ⟨40361750955198160381116683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26907833970132106920744455 40361750955198160381116683)
          ·
            refine ⟨60542626432797240571675025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40361750955198160381116683 60542626432797240571675025)
            ·
              refine ⟨45406969824597930428756269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60542626432797240571675025 45406969824597930428756269)
              ·
                refine ⟨17027613684224223910783601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45406969824597930428756269 17027613684224223910783601)
                ·
                  refine ⟨12770710263168167933087701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17027613684224223910783601 12770710263168167933087701)
                  ·
                    refine ⟨299313521793003935931743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12770710263168167933087701 299313521793003935931743)
                    ·
                      rfl

theorem cell23_1748733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1748733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748733 prefixEnd_1748733 := by exact prefixLift 1748733
  have htrace : WordTrace (prefixWord ++ tailWord_1748733) baseStart_1748733 baseEnd_1748733 := by
    simpa [prefixWord, tailWord_1748733, baseEnd_1748733] using wordTrace_append hprefix tailTrace_1748733
  have hstable : (prefixWord ++ tailWord_1748733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748733).length < 2 ^ (prefixWord ++ tailWord_1748733).sum := by decide
  have hdescent : baseEnd_1748733 < baseStart_1748733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748747 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 3]
def baseStart_1748747 : Nat := 118140960795 + 1748747 * 2 ^ 59
def prefixEnd_1748747 : Nat := 4983230072969 + 3 ^ 40 * 1748747 * 2
def baseEnd_1748747 : Nat := 897947754108174753020165

theorem tailTrace_1748747 : CollatzResearch.WordTrace tailWord_1748747 prefixEnd_1748747 897947754108174753020165 := by
  unfold tailWord_1748747
  simp only [CollatzResearch.WordTrace]
  refine ⟨63782042995595756054996495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42521361997063837369997663 63782042995595756054996495)
  ·
    refine ⟨95673064493393634082494743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63782042995595756054996495 95673064493393634082494743)
    ·
      refine ⟨143509596740090451123742115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95673064493393634082494743 143509596740090451123742115)
      ·
        refine ⟨215264395110135676685613173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143509596740090451123742115 215264395110135676685613173)
        ·
          refine ⟨20181037041575219689276235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215264395110135676685613173 20181037041575219689276235)
          ·
            refine ⟨30271555562362829533914353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20181037041575219689276235 30271555562362829533914353)
            ·
              refine ⟨22703666671772122150435765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30271555562362829533914353 22703666671772122150435765)
              ·
                refine ⟨2128468750478636451603353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22703666671772122150435765 2128468750478636451603353)
                ·
                  refine ⟨1596351562858977338702515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2128468750478636451603353 1596351562858977338702515)
                  ·
                    refine ⟨2394527344288466008053773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1596351562858977338702515 2394527344288466008053773)
                    ·
                      refine ⟨897947754108174753020165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2394527344288466008053773 897947754108174753020165)
                      ·
                        rfl

theorem cell23_1748747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 3].length) (baseStart_1748747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748747 prefixEnd_1748747 := by exact prefixLift 1748747
  have htrace : WordTrace (prefixWord ++ tailWord_1748747) baseStart_1748747 baseEnd_1748747 := by
    simpa [prefixWord, tailWord_1748747, baseEnd_1748747] using wordTrace_append hprefix tailTrace_1748747
  have hstable : (prefixWord ++ tailWord_1748747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748747).length < 2 ^ (prefixWord ++ tailWord_1748747).sum := by decide
  have hdescent : baseEnd_1748747 < baseStart_1748747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748754 : List Nat := [3, 2, 4, 1, 1, 3, 2, 7]
def baseStart_1748754 : Nat := 118140960795 + 1748754 * 2 ^ 59
def prefixEnd_1748754 : Nat := 4983230072969 + 3 ^ 40 * 1748754 * 2
def baseEnd_1748754 : Nat := 33257457350842823171579

theorem tailTrace_1748754 : CollatzResearch.WordTrace tailWord_1748754 prefixEnd_1748754 33257457350842823171579 := by
  unfold tailWord_1748754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15945574576642599062625329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42521532204380264167000877 15945574576642599062625329)
  ·
    refine ⟨11959180932481949296968997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15945574576642599062625329 11959180932481949296968997)
    ·
      refine ⟨2242346424840365493181687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11959180932481949296968997 2242346424840365493181687)
      ·
        refine ⟨3363519637260548239772531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242346424840365493181687 3363519637260548239772531)
        ·
          refine ⟨5045279455890822359658797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3363519637260548239772531 5045279455890822359658797)
          ·
            refine ⟨1891979795959058384872049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5045279455890822359658797 1891979795959058384872049)
            ·
              refine ⟨1418984846969293788654037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891979795959058384872049 1418984846969293788654037)
              ·
                refine ⟨33257457350842823171579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1418984846969293788654037 33257457350842823171579)
                ·
                  rfl

theorem cell23_1748754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 7].length) (baseStart_1748754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748754 prefixEnd_1748754 := by exact prefixLift 1748754
  have htrace : WordTrace (prefixWord ++ tailWord_1748754) baseStart_1748754 baseEnd_1748754 := by
    simpa [prefixWord, tailWord_1748754, baseEnd_1748754] using wordTrace_append hprefix tailTrace_1748754
  have hstable : (prefixWord ++ tailWord_1748754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748754).length < 2 ^ (prefixWord ++ tailWord_1748754).sum := by decide
  have hdescent : baseEnd_1748754 < baseStart_1748754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748798 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_1748798 : Nat := 118140960795 + 1748798 * 2 ^ 59
def prefixEnd_1748798 : Nat := 4983230072969 + 3 ^ 40 * 1748798 * 2
def baseEnd_1748798 : Nat := 897973941621554053482431

theorem tailTrace_1748798 : CollatzResearch.WordTrace tailWord_1748798 prefixEnd_1748798 897973941621554053482431 := by
  unfold tailWord_1748798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7972987889801373970637881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42522602078940661176735365 7972987889801373970637881)
  ·
    refine ⟨5979740917351030477978411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7972987889801373970637881 5979740917351030477978411)
    ·
      refine ⟨8969611376026545716967617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5979740917351030477978411 8969611376026545716967617)
      ·
        refine ⟨6727208532019909287725713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8969611376026545716967617 6727208532019909287725713)
        ·
          refine ⟨5045406399014931965794285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6727208532019909287725713 5045406399014931965794285)
          ·
            refine ⟨1892027399630599487172857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5045406399014931965794285 1892027399630599487172857)
            ·
              refine ⟨1419020549722949615379643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892027399630599487172857 1419020549722949615379643)
              ·
                refine ⟨2128530824584424423069465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419020549722949615379643 2128530824584424423069465)
                ·
                  refine ⟨1596398118438318317302099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2128530824584424423069465 1596398118438318317302099)
                  ·
                    refine ⟨2394597177657477475953149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1596398118438318317302099 2394597177657477475953149)
                    ·
                      refine ⟨897973941621554053482431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2394597177657477475953149 897973941621554053482431)
                      ·
                        rfl

theorem cell23_1748798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_1748798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748798 prefixEnd_1748798 := by exact prefixLift 1748798
  have htrace : WordTrace (prefixWord ++ tailWord_1748798) baseStart_1748798 baseEnd_1748798 := by
    simpa [prefixWord, tailWord_1748798, baseEnd_1748798] using wordTrace_append hprefix tailTrace_1748798
  have hstable : (prefixWord ++ tailWord_1748798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748798).length < 2 ^ (prefixWord ++ tailWord_1748798).sum := by decide
  have hdescent : baseEnd_1748798 < baseStart_1748798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748844 : List Nat := [2, 2, 1, 1, 4, 2, 4, 2, 5]
def baseStart_1748844 : Nat := 118140960795 + 1748844 * 2 ^ 59
def prefixEnd_1748844 : Nat := 4983230072969 + 3 ^ 40 * 1748844 * 2
def baseEnd_1748844 : Nat := 99777506859073430389691

theorem tailTrace_1748844 : CollatzResearch.WordTrace tailWord_1748844 prefixEnd_1748844 99777506859073430389691 := by
  unfold tailWord_1748844
  simp only [CollatzResearch.WordTrace]
  refine ⟨31892790438122170810638793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42523720584162894414185057 31892790438122170810638793)
  ·
    refine ⟨23919592828591628107979095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31892790438122170810638793 23919592828591628107979095)
    ·
      refine ⟨35879389242887442161968643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23919592828591628107979095 35879389242887442161968643)
      ·
        refine ⟨53819083864331163242952965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35879389242887442161968643 53819083864331163242952965)
        ·
          refine ⟨10091078224562093108053681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53819083864331163242952965 10091078224562093108053681)
          ·
            refine ⟨7568308668421569831040261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10091078224562093108053681 7568308668421569831040261)
            ·
              refine ⟨1419057875329044343320049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7568308668421569831040261 1419057875329044343320049)
              ·
                refine ⟨1064293406496783257490037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419057875329044343320049 1064293406496783257490037)
                ·
                  refine ⟨99777506859073430389691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1064293406496783257490037 99777506859073430389691)
                  ·
                    rfl

theorem cell23_1748844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_1748844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748844 prefixEnd_1748844 := by exact prefixLift 1748844
  have htrace : WordTrace (prefixWord ++ tailWord_1748844) baseStart_1748844 baseEnd_1748844 := by
    simpa [prefixWord, tailWord_1748844, baseEnd_1748844] using wordTrace_append hprefix tailTrace_1748844
  have hstable : (prefixWord ++ tailWord_1748844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748844).length < 2 ^ (prefixWord ++ tailWord_1748844).sum := by decide
  have hdescent : baseEnd_1748844 < baseStart_1748844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748920 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1748920 : Nat := 118140960795 + 1748920 * 2 ^ 59
def prefixEnd_1748920 : Nat := 4983230072969 + 3 ^ 40 * 1748920 * 2
def baseEnd_1748920 : Nat := 898036586261402576156869

theorem tailTrace_1748920 : CollatzResearch.WordTrace tailWord_1748920 prefixEnd_1748920 898036586261402576156869 := by
  unfold tailWord_1748920
  simp only [CollatzResearch.WordTrace]
  refine ⟨31894176411984503300522107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42525568549312671067362809 31894176411984503300522107)
  ·
    refine ⟨47841264617976754950783161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31894176411984503300522107 47841264617976754950783161)
    ·
      refine ⟨35880948463482566213087371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47841264617976754950783161 35880948463482566213087371)
      ·
        refine ⟨53821422695223849319631057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35880948463482566213087371 53821422695223849319631057)
        ·
          refine ⟨40366067021417886989723293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53821422695223849319631057 40366067021417886989723293)
          ·
            refine ⟨15137275133031707621146235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40366067021417886989723293 15137275133031707621146235)
            ·
              refine ⟨22705912699547561431719353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15137275133031707621146235 22705912699547561431719353)
              ·
                refine ⟨17029434524660671073789515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22705912699547561431719353 17029434524660671073789515)
                ·
                  refine ⟨25544151786991006610684273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17029434524660671073789515 25544151786991006610684273)
                  ·
                    refine ⟨19158113840243254958013205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25544151786991006610684273 19158113840243254958013205)
                    ·
                      refine ⟨898036586261402576156869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19158113840243254958013205 898036586261402576156869)
                      ·
                        rfl

theorem cell23_1748920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1748920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748920 prefixEnd_1748920 := by exact prefixLift 1748920
  have htrace : WordTrace (prefixWord ++ tailWord_1748920) baseStart_1748920 baseEnd_1748920 := by
    simpa [prefixWord, tailWord_1748920, baseEnd_1748920] using wordTrace_append hprefix tailTrace_1748920
  have hstable : (prefixWord ++ tailWord_1748920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748920).length < 2 ^ (prefixWord ++ tailWord_1748920).sum := by decide
  have hdescent : baseEnd_1748920 < baseStart_1748920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748961 : List Nat := [1, 2, 3, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_1748961 : Nat := 118140960795 + 1748961 * 2 ^ 59
def prefixEnd_1748961 : Nat := 4983230072969 + 3 ^ 40 * 1748961 * 2
def baseEnd_1748961 : Nat := 898057638968236915744181

theorem tailTrace_1748961 : CollatzResearch.WordTrace tailWord_1748961 prefixEnd_1748961 898057638968236915744181 := by
  unfold tailWord_1748961
  simp only [CollatzResearch.WordTrace]
  refine ⟨63789848216820470603286737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42526565477880313735524491 63789848216820470603286737)
  ·
    refine ⟨47842386162615352952465053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63789848216820470603286737 47842386162615352952465053)
    ·
      refine ⟨17940894810980757357174395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47842386162615352952465053 17940894810980757357174395)
      ·
        refine ⟨26911342216471136035761593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17940894810980757357174395 26911342216471136035761593)
        ·
          refine ⟨20183506662353352026821195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26911342216471136035761593 20183506662353352026821195)
          ·
            refine ⟨30275259993530028040231793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20183506662353352026821195 30275259993530028040231793)
            ·
              refine ⟨22706444995147521030173845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30275259993530028040231793 22706444995147521030173845)
              ·
                refine ⟨1064364609147540048289399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22706444995147521030173845 1064364609147540048289399)
                ·
                  refine ⟨1596546913721310072434099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064364609147540048289399 1596546913721310072434099)
                  ·
                    refine ⟨2394820370581965108651149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1596546913721310072434099 2394820370581965108651149)
                    ·
                      refine ⟨898057638968236915744181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2394820370581965108651149 898057638968236915744181)
                      ·
                        rfl

theorem cell23_1748961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_1748961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748961 prefixEnd_1748961 := by exact prefixLift 1748961
  have htrace : WordTrace (prefixWord ++ tailWord_1748961) baseStart_1748961 baseEnd_1748961 := by
    simpa [prefixWord, tailWord_1748961, baseEnd_1748961] using wordTrace_append hprefix tailTrace_1748961
  have hstable : (prefixWord ++ tailWord_1748961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748961).length < 2 ^ (prefixWord ++ tailWord_1748961).sum := by decide
  have hdescent : baseEnd_1748961 < baseStart_1748961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748984 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_1748984 : Nat := 118140960795 + 1748984 * 2 ^ 59
def prefixEnd_1748984 : Nat := 4983230072969 + 3 ^ 40 * 1748984 * 2
def baseEnd_1748984 : Nat := 898069449023290325756575

theorem tailTrace_1748984 : CollatzResearch.WordTrace tailWord_1748984 prefixEnd_1748984 898069449023290325756575 := by
  unfold tailWord_1748984
  simp only [CollatzResearch.WordTrace]
  refine ⟨31895343547868572765687003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42527124730491430354249337 31895343547868572765687003)
  ·
    refine ⟨47843015321802859148530505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31895343547868572765687003 47843015321802859148530505)
    ·
      refine ⟨35882261491352144361397879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47843015321802859148530505 35882261491352144361397879)
      ·
        refine ⟨53823392237028216542096819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35882261491352144361397879 53823392237028216542096819)
        ·
          refine ⟨80735088355542324813145229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53823392237028216542096819 80735088355542324813145229)
          ·
            refine ⟨30275658133328371804929461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80735088355542324813145229 30275658133328371804929461)
            ·
              refine ⟨2838342949999534856712137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30275658133328371804929461 2838342949999534856712137)
              ·
                refine ⟨2128757212499651142534103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2838342949999534856712137 2128757212499651142534103)
                ·
                  refine ⟨3193135818749476713801155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128757212499651142534103 3193135818749476713801155)
                  ·
                    refine ⟨4789703728124215070701733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3193135818749476713801155 4789703728124215070701733)
                    ·
                      refine ⟨898069449023290325756575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4789703728124215070701733 898069449023290325756575)
                      ·
                        rfl

theorem cell23_1748984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_1748984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748984 prefixEnd_1748984 := by exact prefixLift 1748984
  have htrace : WordTrace (prefixWord ++ tailWord_1748984) baseStart_1748984 baseEnd_1748984 := by
    simpa [prefixWord, tailWord_1748984, baseEnd_1748984] using wordTrace_append hprefix tailTrace_1748984
  have hstable : (prefixWord ++ tailWord_1748984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748984).length < 2 ^ (prefixWord ++ tailWord_1748984).sum := by decide
  have hdescent : baseEnd_1748984 < baseStart_1748984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748997 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_1748997 : Nat := 118140960795 + 1748997 * 2 ^ 59
def prefixEnd_1748997 : Nat := 4983230072969 + 3 ^ 40 * 1748997 * 2
def baseEnd_1748997 : Nat := 898076124271798774894015

theorem tailTrace_1748997 : CollatzResearch.WordTrace tailWord_1748997 prefixEnd_1748997 898076124271798774894015 := by
  unfold tailWord_1748997
  simp only [CollatzResearch.WordTrace]
  refine ⟨63791161244690048751597245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42527440829793365834398163 63791161244690048751597245)
  ·
    refine ⟨23921685466758768281848967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63791161244690048751597245 23921685466758768281848967)
    ·
      refine ⟨35882528200138152422773451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23921685466758768281848967 35882528200138152422773451)
      ·
        refine ⟨53823792300207228634160177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35882528200138152422773451 53823792300207228634160177)
        ·
          refine ⟨40367844225155421475620133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53823792300207228634160177 40367844225155421475620133)
          ·
            refine ⟨7568970792216641526678775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40367844225155421475620133 7568970792216641526678775)
            ·
              refine ⟨11353456188324962290018163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7568970792216641526678775 11353456188324962290018163)
              ·
                refine ⟨17030184282487443435027245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353456188324962290018163 17030184282487443435027245)
                ·
                  refine ⟨6386319105932791288135217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17030184282487443435027245 6386319105932791288135217)
                  ·
                    refine ⟨4789739329449593466101413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6386319105932791288135217 4789739329449593466101413)
                    ·
                      refine ⟨898076124271798774894015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4789739329449593466101413 898076124271798774894015)
                      ·
                        rfl

theorem cell23_1748997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_1748997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1748997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1748997 prefixEnd_1748997 := by exact prefixLift 1748997
  have htrace : WordTrace (prefixWord ++ tailWord_1748997) baseStart_1748997 baseEnd_1748997 := by
    simpa [prefixWord, tailWord_1748997, baseEnd_1748997] using wordTrace_append hprefix tailTrace_1748997
  have hstable : (prefixWord ++ tailWord_1748997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748997).length < 2 ^ (prefixWord ++ tailWord_1748997).sum := by decide
  have hdescent : baseEnd_1748997 < baseStart_1748997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749012 : List Nat := [2, 4, 3, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_1749012 : Nat := 118140960795 + 1749012 * 2 ^ 59
def prefixEnd_1749012 : Nat := 4983230072969 + 3 ^ 40 * 1749012 * 2
def baseEnd_1749012 : Nat := 898083826481616216206447

theorem tailTrace_1749012 : CollatzResearch.WordTrace tailWord_1749012 prefixEnd_1749012 898083826481616216206447 := by
  unfold tailWord_1749012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31895854169817853156696645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42527805559757137542262193 31895854169817853156696645)
  ·
    refine ⟨5980472656840847466880621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31895854169817853156696645 5980472656840847466880621)
    ·
      refine ⟨2242677246315317800080233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5980472656840847466880621 2242677246315317800080233)
      ·
        refine ⟨1682007934736488350060175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242677246315317800080233 1682007934736488350060175)
        ·
          refine ⟨2523011902104732525090263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682007934736488350060175 2523011902104732525090263)
          ·
            refine ⟨3784517853157098787635395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523011902104732525090263 3784517853157098787635395)
            ·
              refine ⟨5676776779735648181453093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784517853157098787635395 5676776779735648181453093)
              ·
                refine ⟨1064395646200434034022455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5676776779735648181453093 1064395646200434034022455)
                ·
                  refine ⟨1596593469300651051033683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064395646200434034022455 1596593469300651051033683)
                  ·
                    refine ⟨2394890203950976576550525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1596593469300651051033683 2394890203950976576550525)
                    ·
                      refine ⟨898083826481616216206447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2394890203950976576550525 898083826481616216206447)
                      ·
                        rfl

theorem cell23_1749012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_1749012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749012 prefixEnd_1749012 := by exact prefixLift 1749012
  have htrace : WordTrace (prefixWord ++ tailWord_1749012) baseStart_1749012 baseEnd_1749012 := by
    simpa [prefixWord, tailWord_1749012, baseEnd_1749012] using wordTrace_append hprefix tailTrace_1749012
  have hstable : (prefixWord ++ tailWord_1749012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749012).length < 2 ^ (prefixWord ++ tailWord_1749012).sum := by decide
  have hdescent : baseEnd_1749012 < baseStart_1749012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749017 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 3]
def baseStart_1749017 : Nat := 118140960795 + 1749017 * 2 ^ 59
def prefixEnd_1749017 : Nat := 4983230072969 + 3 ^ 40 * 1749017 * 2
def baseEnd_1749017 : Nat := 898086393884888696643923

theorem tailTrace_1749017 : CollatzResearch.WordTrace tailWord_1749017 prefixEnd_1749017 898086393884888696643923 := by
  unfold tailWord_1749017
  simp only [CollatzResearch.WordTrace]
  refine ⟨63791890704617592167325305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42527927136411728111550203 63791890704617592167325305)
  ·
    refine ⟨47843918028463194125493979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63791890704617592167325305 47843918028463194125493979)
    ·
      refine ⟨71765877042694791188240969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47843918028463194125493979 71765877042694791188240969)
      ·
        refine ⟨53824407782021093391180727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71765877042694791188240969 53824407782021093391180727)
        ·
          refine ⟨80736611673031640086771091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53824407782021093391180727 80736611673031640086771091)
          ·
            refine ⟨121104917509547460130156637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80736611673031640086771091 121104917509547460130156637)
            ·
              refine ⟨45414344066080297548808739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121104917509547460130156637 45414344066080297548808739)
              ·
                refine ⟨68121516099120446323213109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45414344066080297548808739 68121516099120446323213109)
                ·
                  refine ⟨6386392134292541842801229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68121516099120446323213109 6386392134292541842801229)
                  ·
                    refine ⟨2394897050359703191050461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6386392134292541842801229 2394897050359703191050461)
                    ·
                      refine ⟨898086393884888696643923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2394897050359703191050461 898086393884888696643923)
                      ·
                        rfl

theorem cell23_1749017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_1749017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749017 prefixEnd_1749017 := by exact prefixLift 1749017
  have htrace : WordTrace (prefixWord ++ tailWord_1749017) baseStart_1749017 baseEnd_1749017 := by
    simpa [prefixWord, tailWord_1749017, baseEnd_1749017] using wordTrace_append hprefix tailTrace_1749017
  have hstable : (prefixWord ++ tailWord_1749017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749017).length < 2 ^ (prefixWord ++ tailWord_1749017).sum := by decide
  have hdescent : baseEnd_1749017 < baseStart_1749017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749084 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1749084 : Nat := 118140960795 + 1749084 * 2 ^ 59
def prefixEnd_1749084 : Nat := 4983230072969 + 3 ^ 40 * 1749084 * 2
def baseEnd_1749084 : Nat := 299373599029579978168705

theorem tailTrace_1749084 : CollatzResearch.WordTrace tailWord_1749084 prefixEnd_1749084 299373599029579978168705 := by
  unfold tailWord_1749084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31897167197687431305007153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42529556263583241740009537 31897167197687431305007153)
  ·
    refine ⟨23922875398265573478755365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31897167197687431305007153 23922875398265573478755365)
    ·
      refine ⟨4485539137174795027266631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23922875398265573478755365 4485539137174795027266631)
      ·
        refine ⟨6728308705762192540899947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485539137174795027266631 6728308705762192540899947)
        ·
          refine ⟨10092463058643288811349921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728308705762192540899947 10092463058643288811349921)
          ·
            refine ⟨7569347293982466608512441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10092463058643288811349921 7569347293982466608512441)
            ·
              refine ⟨5677010470486849956384331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7569347293982466608512441 5677010470486849956384331)
              ·
                refine ⟨8515515705730274934576497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677010470486849956384331 8515515705730274934576497)
                ·
                  refine ⟨6386636779297706200932373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8515515705730274934576497 6386636779297706200932373)
                  ·
                    refine ⟨299373599029579978168705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6386636779297706200932373 299373599029579978168705)
                    ·
                      rfl

theorem cell23_1749084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1749084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749084 prefixEnd_1749084 := by exact prefixLift 1749084
  have htrace : WordTrace (prefixWord ++ tailWord_1749084) baseStart_1749084 baseEnd_1749084 := by
    simpa [prefixWord, tailWord_1749084, baseEnd_1749084] using wordTrace_append hprefix tailTrace_1749084
  have hstable : (prefixWord ++ tailWord_1749084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749084).length < 2 ^ (prefixWord ++ tailWord_1749084).sum := by decide
  have hdescent : baseEnd_1749084 < baseStart_1749084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749087 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1749087 : Nat := 118140960795 + 1749087 * 2 ^ 59
def prefixEnd_1749087 : Nat := 4983230072969 + 3 ^ 40 * 1749087 * 2
def baseEnd_1749087 : Nat := 898122337530703422768601

theorem tailTrace_1749087 : CollatzResearch.WordTrace tailWord_1749087 prefixEnd_1749087 898122337530703422768601 := by
  unfold tailWord_1749087
  simp only [CollatzResearch.WordTrace]
  refine ⟨63794443814363994122373515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42529629209575996081582343 63794443814363994122373515)
  ·
    refine ⟨95691665721545991183560273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63794443814363994122373515 95691665721545991183560273)
    ·
      refine ⟨71768749291159493387670205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95691665721545991183560273 71768749291159493387670205)
      ·
        refine ⟨26913280984184810020376327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71768749291159493387670205 26913280984184810020376327)
        ·
          refine ⟨40369921476277215030564491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26913280984184810020376327 40369921476277215030564491)
          ·
            refine ⟨60554882214415822545846737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40369921476277215030564491 60554882214415822545846737)
            ·
              refine ⟨45416161660811866909385053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60554882214415822545846737 45416161660811866909385053)
              ·
                refine ⟨17031060622804450091019395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45416161660811866909385053 17031060622804450091019395)
                ·
                  refine ⟨25546590934206675136529093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17031060622804450091019395 25546590934206675136529093)
                  ·
                    refine ⟨4789985800163751588099205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25546590934206675136529093 4789985800163751588099205)
                    ·
                      refine ⟨898122337530703422768601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4789985800163751588099205 898122337530703422768601)
                      ·
                        rfl

theorem cell23_1749087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1749087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749087 prefixEnd_1749087 := by exact prefixLift 1749087
  have htrace : WordTrace (prefixWord ++ tailWord_1749087) baseStart_1749087 baseEnd_1749087 := by
    simpa [prefixWord, tailWord_1749087, baseEnd_1749087] using wordTrace_append hprefix tailTrace_1749087
  have hstable : (prefixWord ++ tailWord_1749087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749087).length < 2 ^ (prefixWord ++ tailWord_1749087).sum := by decide
  have hdescent : baseEnd_1749087 < baseStart_1749087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749091 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 1, 4, 2]
def baseStart_1749091 : Nat := 118140960795 + 1749091 * 2 ^ 59
def prefixEnd_1749091 : Nat := 4983230072969 + 3 ^ 40 * 1749091 * 2
def baseEnd_1749091 : Nat := 898124391453321407118583

theorem tailTrace_1749091 : CollatzResearch.WordTrace tailWord_1749091 prefixEnd_1749091 898124391453321407118583 := by
  unfold tailWord_1749091
  simp only [CollatzResearch.WordTrace]
  refine ⟨63794589706349502805519127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42529726470899668537012751 63794589706349502805519127)
  ·
    refine ⟨95691884559524254208278691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63794589706349502805519127 95691884559524254208278691)
    ·
      refine ⟨143537826839286381312418037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95691884559524254208278691 143537826839286381312418037)
      ·
        refine ⟨13456671266183098248039191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143537826839286381312418037 13456671266183098248039191)
        ·
          refine ⟨20185006899274647372058787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13456671266183098248039191 20185006899274647372058787)
          ·
            refine ⟨30277510348911971058088181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20185006899274647372058787 30277510348911971058088181)
            ·
              refine ⟨2838516595210497286695767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30277510348911971058088181 2838516595210497286695767)
              ·
                refine ⟨4257774892815745930043651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838516595210497286695767 4257774892815745930043651)
                ·
                  refine ⟨6386662339223618895065477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4257774892815745930043651 6386662339223618895065477)
                  ·
                    refine ⟨1197499188604428542824777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6386662339223618895065477 1197499188604428542824777)
                    ·
                      refine ⟨898124391453321407118583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197499188604428542824777 898124391453321407118583)
                      ·
                        rfl

theorem cell23_1749091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_1749091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749091 prefixEnd_1749091 := by exact prefixLift 1749091
  have htrace : WordTrace (prefixWord ++ tailWord_1749091) baseStart_1749091 baseEnd_1749091 := by
    simpa [prefixWord, tailWord_1749091, baseEnd_1749091] using wordTrace_append hprefix tailTrace_1749091
  have hstable : (prefixWord ++ tailWord_1749091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749091).length < 2 ^ (prefixWord ++ tailWord_1749091).sum := by decide
  have hdescent : baseEnd_1749091 < baseStart_1749091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749097 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 7]
def baseStart_1749097 : Nat := 118140960795 + 1749097 * 2 ^ 59
def prefixEnd_1749097 : Nat := 4983230072969 + 3 ^ 40 * 1749097 * 2
def baseEnd_1749097 : Nat := 99791941370805375960395

theorem tailTrace_1749097 : CollatzResearch.WordTrace tailWord_1749097 prefixEnd_1749097 99791941370805375960395 := by
  unfold tailWord_1749097
  simp only [CollatzResearch.WordTrace]
  refine ⟨63794808544327765830237545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42529872362885177220158363 63794808544327765830237545)
  ·
    refine ⟨47846106408245824372678159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63794808544327765830237545 47846106408245824372678159)
    ·
      refine ⟨71769159612368736559017239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47846106408245824372678159 71769159612368736559017239)
      ·
        refine ⟨107653739418553104838525859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71769159612368736559017239 107653739418553104838525859)
        ·
          refine ⟨161480609127829657257788789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107653739418553104838525859 161480609127829657257788789)
          ·
            refine ⟨15138807105734030367917699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161480609127829657257788789 15138807105734030367917699)
            ·
              refine ⟨22708210658601045551876549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15138807105734030367917699 22708210658601045551876549)
              ·
                refine ⟨4257789498487696040976853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22708210658601045551876549 4257789498487696040976853)
                ·
                  refine ⟨99791941370805375960395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4257789498487696040976853 99791941370805375960395)
                  ·
                    rfl

theorem cell23_1749097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_1749097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749097 prefixEnd_1749097 := by exact prefixLift 1749097
  have htrace : WordTrace (prefixWord ++ tailWord_1749097) baseStart_1749097 baseEnd_1749097 := by
    simpa [prefixWord, tailWord_1749097, baseEnd_1749097] using wordTrace_append hprefix tailTrace_1749097
  have hstable : (prefixWord ++ tailWord_1749097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749097).length < 2 ^ (prefixWord ++ tailWord_1749097).sum := by decide
  have hdescent : baseEnd_1749097 < baseStart_1749097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749181 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_1749181 : Nat := 118140960795 + 1749181 * 2 ^ 59
def prefixEnd_1749181 : Nat := 4983230072969 + 3 ^ 40 * 1749181 * 2
def baseEnd_1749181 : Nat := 898170604712226054993169

theorem tailTrace_1749181 : CollatzResearch.WordTrace tailWord_1749181 prefixEnd_1749181 898170604712226054993169 := by
  unfold tailWord_1749181
  simp only [CollatzResearch.WordTrace]
  refine ⟨63797872276023448176295397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42531914850682298784196931 63797872276023448176295397)
  ·
    refine ⟨11962101051754396533055387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63797872276023448176295397 11962101051754396533055387)
    ·
      refine ⟨17943151577631594799583081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11962101051754396533055387 17943151577631594799583081)
      ·
        refine ⟨13457363683223696099687311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17943151577631594799583081 13457363683223696099687311)
        ·
          refine ⟨20186045524835544149530967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13457363683223696099687311 20186045524835544149530967)
          ·
            refine ⟨30279068287253316224296451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20186045524835544149530967 30279068287253316224296451)
            ·
              refine ⟨45418602430879974336444677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30279068287253316224296451 45418602430879974336444677)
              ·
                refine ⟨8515987955789995188083377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45418602430879974336444677 8515987955789995188083377)
                ·
                  refine ⟨6386990966842496391062533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8515987955789995188083377 6386990966842496391062533)
                  ·
                    refine ⟨1197560806282968073324225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6386990966842496391062533 1197560806282968073324225)
                    ·
                      refine ⟨898170604712226054993169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197560806282968073324225 898170604712226054993169)
                      ·
                        rfl

theorem cell23_1749181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_1749181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749181 prefixEnd_1749181 := by exact prefixLift 1749181
  have htrace : WordTrace (prefixWord ++ tailWord_1749181) baseStart_1749181 baseEnd_1749181 := by
    simpa [prefixWord, tailWord_1749181, baseEnd_1749181] using wordTrace_append hprefix tailTrace_1749181
  have hstable : (prefixWord ++ tailWord_1749181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749181).length < 2 ^ (prefixWord ++ tailWord_1749181).sum := by decide
  have hdescent : baseEnd_1749181 < baseStart_1749181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749182 : List Nat := [4, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_1749182 : Nat := 118140960795 + 1749182 * 2 ^ 59
def prefixEnd_1749182 : Nat := 4983230072969 + 3 ^ 40 * 1749182 * 2
def baseEnd_1749182 : Nat := 99796790910320061231185

theorem tailTrace_1749182 : CollatzResearch.WordTrace tailWord_1749182 prefixEnd_1749182 99796790910320061231185 := by
  unfold tailWord_1749182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7974738593627478168385225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42531939166013216898054533 7974738593627478168385225)
  ·
    refine ⟨5981053945220608626288919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7974738593627478168385225 5981053945220608626288919)
    ·
      refine ⟨8971580917830912939433379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5981053945220608626288919 8971580917830912939433379)
      ·
        refine ⟨13457371376746369409150069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8971580917830912939433379 13457371376746369409150069)
        ·
          refine ⟨1261628566569972132107819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13457371376746369409150069 1261628566569972132107819)
          ·
            refine ⟨1892442849854958198161729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261628566569972132107819 1892442849854958198161729)
            ·
              refine ⟨1419332137391218648621297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892442849854958198161729 1419332137391218648621297)
              ·
                refine ⟨1064499103043413986465973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419332137391218648621297 1064499103043413986465973)
                ·
                  refine ⟨99796790910320061231185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1064499103043413986465973 99796790910320061231185)
                  ·
                    rfl

theorem cell23_1749182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_1749182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749182 prefixEnd_1749182 := by exact prefixLift 1749182
  have htrace : WordTrace (prefixWord ++ tailWord_1749182) baseStart_1749182 baseEnd_1749182 := by
    simpa [prefixWord, tailWord_1749182, baseEnd_1749182] using wordTrace_append hprefix tailTrace_1749182
  have hstable : (prefixWord ++ tailWord_1749182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749182).length < 2 ^ (prefixWord ++ tailWord_1749182).sum := by decide
  have hdescent : baseEnd_1749182 < baseStart_1749182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749187 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 12]
def baseStart_1749187 : Nat := 118140960795 + 1749187 * 2 ^ 59
def prefixEnd_1749187 : Nat := 4983230072969 + 3 ^ 40 * 1749187 * 2
def baseEnd_1749187 : Nat := 99797076177350336835349

theorem tailTrace_1749187 : CollatzResearch.WordTrace tailWord_1749187 prefixEnd_1749187 99797076177350336835349 := by
  unfold tailWord_1749187
  simp only [CollatzResearch.WordTrace]
  refine ⟨63798091114001711201013815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42532060742667807467342543 63798091114001711201013815)
  ·
    refine ⟨95697136671002566801520723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63798091114001711201013815 95697136671002566801520723)
    ·
      refine ⟨143545705006503850202281085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95697136671002566801520723 143545705006503850202281085)
      ·
        refine ⟨53829639377438943825855407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143545705006503850202281085 53829639377438943825855407)
        ·
          refine ⟨80744459066158415738783111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53829639377438943825855407 80744459066158415738783111)
          ·
            refine ⟨121116688599237623608174667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80744459066158415738783111 121116688599237623608174667)
            ·
              refine ⟨181675032898856435412262001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121116688599237623608174667 181675032898856435412262001)
              ·
                refine ⟨136256274674142326559196501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181675032898856435412262001 136256274674142326559196501)
                ·
                  refine ⟨99797076177350336835349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 136256274674142326559196501 99797076177350336835349)
                  ·
                    rfl

theorem cell23_1749187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 12].length) (baseStart_1749187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749187 prefixEnd_1749187 := by exact prefixLift 1749187
  have htrace : WordTrace (prefixWord ++ tailWord_1749187) baseStart_1749187 baseEnd_1749187 := by
    simpa [prefixWord, tailWord_1749187, baseEnd_1749187] using wordTrace_append hprefix tailTrace_1749187
  have hstable : (prefixWord ++ tailWord_1749187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749187).length < 2 ^ (prefixWord ++ tailWord_1749187).sum := by decide
  have hdescent : baseEnd_1749187 < baseStart_1749187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749198 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_1749198 : Nat := 118140960795 + 1749198 * 2 ^ 59
def prefixEnd_1749198 : Nat := 4983230072969 + 3 ^ 40 * 1749198 * 2
def baseEnd_1749198 : Nat := 898179333883352488480591

theorem tailTrace_1749198 : CollatzResearch.WordTrace tailWord_1749198 prefixEnd_1749198 898179333883352488480591 := by
  unfold tailWord_1749198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7974811539620232509958031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42532328211307906719776165 7974811539620232509958031)
  ·
    refine ⟨11962217309430348764937047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7974811539620232509958031 11962217309430348764937047)
    ·
      refine ⟨17943325964145523147405571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11962217309430348764937047 17943325964145523147405571)
      ·
        refine ⟨26914988946218284721108357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17943325964145523147405571 26914988946218284721108357)
        ·
          refine ⟨5046560427415928385207817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26914988946218284721108357 5046560427415928385207817)
          ·
            refine ⟨3784920320561946288905863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5046560427415928385207817 3784920320561946288905863)
            ·
              refine ⟨5677380480842919433358795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784920320561946288905863 5677380480842919433358795)
              ·
                refine ⟨8516070721264379150038193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677380480842919433358795 8516070721264379150038193)
                ·
                  refine ⟨6387053040948284362528645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8516070721264379150038193 6387053040948284362528645)
                  ·
                    refine ⟨1197572445177803317974121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387053040948284362528645 1197572445177803317974121)
                    ·
                      refine ⟨898179333883352488480591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197572445177803317974121 898179333883352488480591)
                      ·
                        rfl

theorem cell23_1749198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_1749198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749198 prefixEnd_1749198 := by exact prefixLift 1749198
  have htrace : WordTrace (prefixWord ++ tailWord_1749198) baseStart_1749198 baseEnd_1749198 := by
    simpa [prefixWord, tailWord_1749198, baseEnd_1749198] using wordTrace_append hprefix tailTrace_1749198
  have hstable : (prefixWord ++ tailWord_1749198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749198).length < 2 ^ (prefixWord ++ tailWord_1749198).sum := by decide
  have hdescent : baseEnd_1749198 < baseStart_1749198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749212 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1749212 : Nat := 118140960795 + 1749212 * 2 ^ 59
def prefixEnd_1749212 : Nat := 4983230072969 + 3 ^ 40 * 1749212 * 2
def baseEnd_1749212 : Nat := 299395507537505144568509

theorem tailTrace_1749212 : CollatzResearch.WordTrace tailWord_1749212 prefixEnd_1749212 299395507537505144568509 := by
  unfold tailWord_1749212
  simp only [CollatzResearch.WordTrace]
  refine ⟨31899501469455570235336945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42532668625940760313782593 31899501469455570235336945)
  ·
    refine ⟨23924626102091677676502709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31899501469455570235336945 23924626102091677676502709)
    ·
      refine ⟨2242933697071094782172129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23924626102091677676502709 2242933697071094782172129)
      ·
        refine ⟨1682200272803321086629097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242933697071094782172129 1682200272803321086629097)
        ·
          refine ⟨1261650204602490814971823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682200272803321086629097 1261650204602490814971823)
          ·
            refine ⟨1892475306903736222457735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261650204602490814971823 1892475306903736222457735)
            ·
              refine ⟨2838712960355604333686603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892475306903736222457735 2838712960355604333686603)
              ·
                refine ⟨4258069440533406500529905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838712960355604333686603 4258069440533406500529905)
                ·
                  refine ⟨3193552080400054875397429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258069440533406500529905 3193552080400054875397429)
                  ·
                    refine ⟨299395507537505144568509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3193552080400054875397429 299395507537505144568509)
                    ·
                      rfl

theorem cell23_1749212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1749212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749212 prefixEnd_1749212 := by exact prefixLift 1749212
  have htrace : WordTrace (prefixWord ++ tailWord_1749212) baseStart_1749212 baseEnd_1749212 := by
    simpa [prefixWord, tailWord_1749212, baseEnd_1749212] using wordTrace_append hprefix tailTrace_1749212
  have hstable : (prefixWord ++ tailWord_1749212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749212).length < 2 ^ (prefixWord ++ tailWord_1749212).sum := by decide
  have hdescent : baseEnd_1749212 < baseStart_1749212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749255 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 6]
def baseStart_1749255 : Nat := 118140960795 + 1749255 * 2 ^ 59
def prefixEnd_1749255 : Nat := 4983230072969 + 3 ^ 40 * 1749255 * 2
def baseEnd_1749255 : Nat := 99800955808962085051981

theorem tailTrace_1749255 : CollatzResearch.WordTrace tailWord_1749255 prefixEnd_1749255 99800955808962085051981 := by
  unfold tailWord_1749255
  simp only [CollatzResearch.WordTrace]
  refine ⟨63800571277755358814489219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42533714185170239209659479 63800571277755358814489219)
  ·
    refine ⟨95700856916633038221733829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63800571277755358814489219 95700856916633038221733829)
    ·
      refine ⟨17943910671868694666575093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95700856916633038221733829 17943910671868694666575093)
      ·
        refine ⟨1682241625487690124991415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17943910671868694666575093 1682241625487690124991415)
        ·
          refine ⟨2523362438231535187487123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682241625487690124991415 2523362438231535187487123)
          ·
            refine ⟨3785043657347302781230685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523362438231535187487123 3785043657347302781230685)
            ·
              refine ⟨1419391371505238542961507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3785043657347302781230685 1419391371505238542961507)
              ·
                refine ⟨2129087057257857814442261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419391371505238542961507 2129087057257857814442261)
                ·
                  refine ⟨99800955808962085051981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2129087057257857814442261 99800955808962085051981)
                  ·
                    rfl

theorem cell23_1749255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 6].length) (baseStart_1749255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749255 prefixEnd_1749255 := by exact prefixLift 1749255
  have htrace : WordTrace (prefixWord ++ tailWord_1749255) baseStart_1749255 baseEnd_1749255 := by
    simpa [prefixWord, tailWord_1749255, baseEnd_1749255] using wordTrace_append hprefix tailTrace_1749255
  have hstable : (prefixWord ++ tailWord_1749255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749255).length < 2 ^ (prefixWord ++ tailWord_1749255).sum := by decide
  have hdescent : baseEnd_1749255 < baseStart_1749255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749281 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 4, 4]
def baseStart_1749281 : Nat := 118140960795 + 1749281 * 2 ^ 59
def prefixEnd_1749281 : Nat := 4983230072969 + 3 ^ 40 * 1749281 * 2
def baseEnd_1749281 : Nat := 299407317592558554580903

theorem tailTrace_1749281 : CollatzResearch.WordTrace tailWord_1749281 prefixEnd_1749281 299407317592558554580903 := by
  unfold tailWord_1749281
  simp only [CollatzResearch.WordTrace]
  refine ⟨63801519575661165254935697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42534346383774110169957131 63801519575661165254935697)
  ·
    refine ⟨47851139681745873941201773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63801519575661165254935697 47851139681745873941201773)
    ·
      refine ⟨17944177380654702727950665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47851139681745873941201773 17944177380654702727950665)
      ·
        refine ⟨13458133035491027045962999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17944177380654702727950665 13458133035491027045962999)
        ·
          refine ⟨20187199553236540568944499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13458133035491027045962999 20187199553236540568944499)
          ·
            refine ⟨30280799329854810853416749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20187199553236540568944499 30280799329854810853416749)
            ·
              refine ⟨11355299748695554070031281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30280799329854810853416749 11355299748695554070031281)
              ·
                refine ⟨8516474811521665552523461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11355299748695554070031281 8516474811521665552523461)
                ·
                  refine ⟨1596839027160312291098149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8516474811521665552523461 1596839027160312291098149)
                  ·
                    refine ⟨299407317592558554580903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1596839027160312291098149 299407317592558554580903)
                    ·
                      rfl

theorem cell23_1749281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_1749281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749281 prefixEnd_1749281 := by exact prefixLift 1749281
  have htrace : WordTrace (prefixWord ++ tailWord_1749281) baseStart_1749281 baseEnd_1749281 := by
    simpa [prefixWord, tailWord_1749281, baseEnd_1749281] using wordTrace_append hprefix tailTrace_1749281
  have hstable : (prefixWord ++ tailWord_1749281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749281).length < 2 ^ (prefixWord ++ tailWord_1749281).sum := by decide
  have hdescent : baseEnd_1749281 < baseStart_1749281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749282 : List Nat := [3, 3, 1, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_1749282 : Nat := 118140960795 + 1749282 * 2 ^ 59
def prefixEnd_1749282 : Nat := 4983230072969 + 3 ^ 40 * 1749282 * 2
def baseEnd_1749282 : Nat := 898222466258330159830205

theorem tailTrace_1749282 : CollatzResearch.WordTrace tailWord_1749282 prefixEnd_1749282 898222466258330159830205 := by
  unfold tailWord_1749282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950389012164385606430525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42534370699105028283814733 15950389012164385606430525)
  ·
    refine ⟨5981395879561644602411447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15950389012164385606430525 5981395879561644602411447)
    ·
      refine ⟨8972093819342466903617171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5981395879561644602411447 8972093819342466903617171)
      ·
        refine ⟨13458140729013700355425757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8972093819342466903617171 13458140729013700355425757)
        ·
          refine ⟨5046802773380137633284659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13458140729013700355425757 5046802773380137633284659)
          ·
            refine ⟨7570204160070206449926989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046802773380137633284659 7570204160070206449926989)
            ·
              refine ⟨2838826560026327418722621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7570204160070206449926989 2838826560026327418722621)
              ·
                refine ⟨1064559960009872782020983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2838826560026327418722621 1064559960009872782020983)
                ·
                  refine ⟨1596839940014809173031475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064559960009872782020983 1596839940014809173031475)
                  ·
                    refine ⟨2395259910022213759547213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1596839940014809173031475 2395259910022213759547213)
                    ·
                      refine ⟨898222466258330159830205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395259910022213759547213 898222466258330159830205)
                      ·
                        rfl

theorem cell23_1749282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_1749282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749282 prefixEnd_1749282 := by exact prefixLift 1749282
  have htrace : WordTrace (prefixWord ++ tailWord_1749282) baseStart_1749282 baseEnd_1749282 := by
    simpa [prefixWord, tailWord_1749282, baseEnd_1749282] using wordTrace_append hprefix tailTrace_1749282
  have hstable : (prefixWord ++ tailWord_1749282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749282).length < 2 ^ (prefixWord ++ tailWord_1749282).sum := by decide
  have hdescent : baseEnd_1749282 < baseStart_1749282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749321 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 3]
def baseStart_1749321 : Nat := 118140960795 + 1749321 * 2 ^ 59
def prefixEnd_1749321 : Nat := 4983230072969 + 3 ^ 40 * 1749321 * 2
def baseEnd_1749321 : Nat := 898242492003855507242525

theorem tailTrace_1749321 : CollatzResearch.WordTrace tailWord_1749321 prefixEnd_1749321 898242492003855507242525 := by
  unfold tailWord_1749321
  simp only [CollatzResearch.WordTrace]
  refine ⟨63802978495516252086391817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42535318997010834724261211 63802978495516252086391817)
  ·
    refine ⟨47852233871637189064793863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63802978495516252086391817 47852233871637189064793863)
    ·
      refine ⟨71778350807455783597190795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47852233871637189064793863 71778350807455783597190795)
      ·
        refine ⟨107667526211183675395786193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71778350807455783597190795 107667526211183675395786193)
        ·
          refine ⟨80750644658387756546839645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107667526211183675395786193 80750644658387756546839645)
          ·
            refine ⟨30281491746895408705064867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80750644658387756546839645 30281491746895408705064867)
            ·
              refine ⟨45422237620343113057597301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30281491746895408705064867 45422237620343113057597301)
              ·
                refine ⟨4258334776907166849149747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45422237620343113057597301 4258334776907166849149747)
                ·
                  refine ⟨6387502165360750273724621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258334776907166849149747 6387502165360750273724621)
                  ·
                    refine ⟨2395313312010281352646733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6387502165360750273724621 2395313312010281352646733)
                    ·
                      refine ⟨898242492003855507242525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395313312010281352646733 898242492003855507242525)
                      ·
                        rfl

theorem cell23_1749321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_1749321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749321 prefixEnd_1749321 := by exact prefixLift 1749321
  have htrace : WordTrace (prefixWord ++ tailWord_1749321) baseStart_1749321 baseEnd_1749321 := by
    simpa [prefixWord, tailWord_1749321, baseEnd_1749321] using wordTrace_append hprefix tailTrace_1749321
  have hstable : (prefixWord ++ tailWord_1749321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749321).length < 2 ^ (prefixWord ++ tailWord_1749321).sum := by decide
  have hdescent : baseEnd_1749321 < baseStart_1749321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749356 : List Nat := [2, 2, 1, 1, 6, 2, 2, 2, 1, 2, 2]
def baseStart_1749356 : Nat := 118140960795 + 1749356 * 2 ^ 59
def prefixEnd_1749356 : Nat := 4983230072969 + 3 ^ 40 * 1749356 * 2
def baseEnd_1749356 : Nat := 898260463826762870304865

theorem tailTrace_1749356 : CollatzResearch.WordTrace tailWord_1749356 prefixEnd_1749356 898260463826762870304865 := by
  unfold tailWord_1749356
  simp only [CollatzResearch.WordTrace]
  refine ⟨31902127525194726531957961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42536170033592968709277281 31902127525194726531957961)
  ·
    refine ⟨23926595643896044898968471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31902127525194726531957961 23926595643896044898968471)
    ·
      refine ⟨35889893465844067348452707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23926595643896044898968471 35889893465844067348452707)
      ·
        refine ⟨53834840198766101022679061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35889893465844067348452707 53834840198766101022679061)
        ·
          refine ⟨2523508134317160985438081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53834840198766101022679061 2523508134317160985438081)
          ·
            refine ⟨1892631100737870739078561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2523508134317160985438081 1892631100737870739078561)
            ·
              refine ⟨1419473325553403054308921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892631100737870739078561 1419473325553403054308921)
              ·
                refine ⟨1064604994165052290731691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419473325553403054308921 1064604994165052290731691)
                ·
                  refine ⟨1596907491247578436097537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064604994165052290731691 1596907491247578436097537)
                  ·
                    refine ⟨1197680618435683827073153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596907491247578436097537 1197680618435683827073153)
                    ·
                      refine ⟨898260463826762870304865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197680618435683827073153 898260463826762870304865)
                      ·
                        rfl

theorem cell23_1749356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_1749356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749356 prefixEnd_1749356 := by exact prefixLift 1749356
  have htrace : WordTrace (prefixWord ++ tailWord_1749356) baseStart_1749356 baseEnd_1749356 := by
    simpa [prefixWord, tailWord_1749356, baseEnd_1749356] using wordTrace_append hprefix tailTrace_1749356
  have hstable : (prefixWord ++ tailWord_1749356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749356).length < 2 ^ (prefixWord ++ tailWord_1749356).sum := by decide
  have hdescent : baseEnd_1749356 < baseStart_1749356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749365 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_1749365 : Nat := 118140960795 + 1749365 * 2 ^ 59
def prefixEnd_1749365 : Nat := 4983230072969 + 3 ^ 40 * 1749365 * 2
def baseEnd_1749365 : Nat := 898265085152653335092323

theorem tailTrace_1749365 : CollatzResearch.WordTrace tailWord_1749365 prefixEnd_1749365 898265085152653335092323 := by
  unfold tailWord_1749365
  simp only [CollatzResearch.WordTrace]
  refine ⟨63804583307356847600993549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42536388871571231733995699 63804583307356847600993549)
  ·
    refine ⟨23926718740258817850372581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63804583307356847600993549 23926718740258817850372581)
    ·
      refine ⟨4486259763798528346944859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23926718740258817850372581 4486259763798528346944859)
      ·
        refine ⟨6729389645697792520417289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486259763798528346944859 6729389645697792520417289)
        ·
          refine ⟨5047042234273344390312967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6729389645697792520417289 5047042234273344390312967)
          ·
            refine ⟨7570563351410016585469451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047042234273344390312967 7570563351410016585469451)
            ·
              refine ⟨11355845027115024878204177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570563351410016585469451 11355845027115024878204177)
              ·
                refine ⟨8516883770336268658653133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11355845027115024878204177 8516883770336268658653133)
                ·
                  refine ⟨3193831413876100746994925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8516883770336268658653133 3193831413876100746994925)
                  ·
                    refine ⟨1197686780203537780123097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193831413876100746994925 1197686780203537780123097)
                    ·
                      refine ⟨898265085152653335092323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197686780203537780123097 898265085152653335092323)
                      ·
                        rfl

theorem cell23_1749365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_1749365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749365 prefixEnd_1749365 := by exact prefixLift 1749365
  have htrace : WordTrace (prefixWord ++ tailWord_1749365) baseStart_1749365 baseEnd_1749365 := by
    simpa [prefixWord, tailWord_1749365, baseEnd_1749365] using wordTrace_append hprefix tailTrace_1749365
  have hstable : (prefixWord ++ tailWord_1749365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749365).length < 2 ^ (prefixWord ++ tailWord_1749365).sum := by decide
  have hdescent : baseEnd_1749365 < baseStart_1749365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749371 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 2, 6]
def baseStart_1749371 : Nat := 118140960795 + 1749371 * 2 ^ 59
def prefixEnd_1749371 : Nat := 4983230072969 + 3 ^ 40 * 1749371 * 2
def baseEnd_1749371 : Nat := 299422722012193437205765

theorem tailTrace_1749371 : CollatzResearch.WordTrace tailWord_1749371 prefixEnd_1749371 299422722012193437205765 := by
  unfold tailWord_1749371
  simp only [CollatzResearch.WordTrace]
  refine ⟨63804802145335110625711967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42536534763556740417141311 63804802145335110625711967)
  ·
    refine ⟨95707203218002665938567951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63804802145335110625711967 95707203218002665938567951)
    ·
      refine ⟨143560804827003998907851927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95707203218002665938567951 143560804827003998907851927)
      ·
        refine ⟨215341207240505998361777891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143560804827003998907851927 215341207240505998361777891)
        ·
          refine ⟨323011810860758997542666837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215341207240505998361777891 323011810860758997542666837)
          ·
            refine ⟨3785294658524519502453127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 323011810860758997542666837 3785294658524519502453127)
            ·
              refine ⟨5677941987786779253679691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785294658524519502453127 5677941987786779253679691)
              ·
                refine ⟨8516912981680168880519537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677941987786779253679691 8516912981680168880519537)
                ·
                  refine ⟨6387684736260126660389653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8516912981680168880519537 6387684736260126660389653)
                  ·
                    refine ⟨299422722012193437205765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6387684736260126660389653 299422722012193437205765)
                    ·
                      rfl

theorem cell23_1749371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 6].length) (baseStart_1749371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749371 prefixEnd_1749371 := by exact prefixLift 1749371
  have htrace : WordTrace (prefixWord ++ tailWord_1749371) baseStart_1749371 baseEnd_1749371 := by
    simpa [prefixWord, tailWord_1749371, baseEnd_1749371] using wordTrace_append hprefix tailTrace_1749371
  have hstable : (prefixWord ++ tailWord_1749371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749371).length < 2 ^ (prefixWord ++ tailWord_1749371).sum := by decide
  have hdescent : baseEnd_1749371 < baseStart_1749371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749381 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_1749381 : Nat := 118140960795 + 1749381 * 2 ^ 59
def prefixEnd_1749381 : Nat := 4983230072969 + 3 ^ 40 * 1749381 * 2
def baseEnd_1749381 : Nat := 898273300843125272492249

theorem tailTrace_1749381 : CollatzResearch.WordTrace tailWord_1749381 prefixEnd_1749381 898273300843125272492249 := by
  unfold tailWord_1749381
  simp only [CollatzResearch.WordTrace]
  refine ⟨63805166875298882333575997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42536777916865921555717331 63805166875298882333575997)
  ·
    refine ⟨23926937578237080875090999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63805166875298882333575997 23926937578237080875090999)
    ·
      refine ⟨35890406367355621312636499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23926937578237080875090999 35890406367355621312636499)
      ·
        refine ⟨53835609551033431968954749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35890406367355621312636499 53835609551033431968954749)
        ·
          refine ⟨20188353581637536988358031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53835609551033431968954749 20188353581637536988358031)
          ·
            refine ⟨30282530372456305482537047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20188353581637536988358031 30282530372456305482537047)
            ·
              refine ⟨45423795558684458223805571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30282530372456305482537047 45423795558684458223805571)
              ·
                refine ⟨68135693338026687335708357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45423795558684458223805571 68135693338026687335708357)
                ·
                  refine ⟨12775442500880003875445317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68135693338026687335708357 12775442500880003875445317)
                  ·
                    refine ⟨2395395468915000726645997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12775442500880003875445317 2395395468915000726645997)
                    ·
                      refine ⟨898273300843125272492249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395395468915000726645997 898273300843125272492249)
                      ·
                        rfl

theorem cell23_1749381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_1749381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749381 prefixEnd_1749381 := by exact prefixLift 1749381
  have htrace : WordTrace (prefixWord ++ tailWord_1749381) baseStart_1749381 baseEnd_1749381 := by
    simpa [prefixWord, tailWord_1749381, baseEnd_1749381] using wordTrace_append hprefix tailTrace_1749381
  have hstable : (prefixWord ++ tailWord_1749381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749381).length < 2 ^ (prefixWord ++ tailWord_1749381).sum := by decide
  have hdescent : baseEnd_1749381 < baseStart_1749381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749412 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_1749412 : Nat := 118140960795 + 1749412 * 2 ^ 59
def prefixEnd_1749412 : Nat := 4983230072969 + 3 ^ 40 * 1749412 * 2
def baseEnd_1749412 : Nat := 898289218743414651204607

theorem tailTrace_1749412 : CollatzResearch.WordTrace tailWord_1749412 prefixEnd_1749412 898289218743414651204607 := by
  unfold tailWord_1749412
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903148769093287313977245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42537531692124383085302993 31903148769093287313977245)
  ·
    refine ⟨11963680788409982742741467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31903148769093287313977245 11963680788409982742741467)
    ·
      refine ⟨17945521182614974114112201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11963680788409982742741467 17945521182614974114112201)
      ·
        refine ⟨13459140886961230585584151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17945521182614974114112201 13459140886961230585584151)
        ·
          refine ⟨20188711330441845878376227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13459140886961230585584151 20188711330441845878376227)
          ·
            refine ⟨30283066995662768817564341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20188711330441845878376227 30283066995662768817564341)
            ·
              refine ⟨2839037530843384576646657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30283066995662768817564341 2839037530843384576646657)
              ·
                refine ⟨2129278148132538432484993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2839037530843384576646657 2129278148132538432484993)
                ·
                  refine ⟨1596958611099403824363745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2129278148132538432484993 1596958611099403824363745)
                  ·
                    refine ⟨1197718958324552868272809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596958611099403824363745 1197718958324552868272809)
                    ·
                      refine ⟨898289218743414651204607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197718958324552868272809 898289218743414651204607)
                      ·
                        rfl

theorem cell23_1749412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_1749412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749412 prefixEnd_1749412 := by exact prefixLift 1749412
  have htrace : WordTrace (prefixWord ++ tailWord_1749412) baseStart_1749412 baseEnd_1749412 := by
    simpa [prefixWord, tailWord_1749412, baseEnd_1749412] using wordTrace_append hprefix tailTrace_1749412
  have hstable : (prefixWord ++ tailWord_1749412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749412).length < 2 ^ (prefixWord ++ tailWord_1749412).sum := by decide
  have hdescent : baseEnd_1749412 < baseStart_1749412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749429 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_1749429 : Nat := 118140960795 + 1749429 * 2 ^ 59
def prefixEnd_1749429 : Nat := 4983230072969 + 3 ^ 40 * 1749429 * 2
def baseEnd_1749429 : Nat := 898297947914541084692029

theorem tailTrace_1749429 : CollatzResearch.WordTrace tailWord_1749429 prefixEnd_1749429 898297947914541084692029 := by
  unfold tailWord_1749429
  simp only [CollatzResearch.WordTrace]
  refine ⟨63806917579124986531323341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42537945052749991020882227 63806917579124986531323341)
  ·
    refine ⟨23927594092171869949246253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63806917579124986531323341 23927594092171869949246253)
    ·
      refine ⟨8972847784564451230967345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23927594092171869949246253 8972847784564451230967345)
      ·
        refine ⟨6729635838423338423225509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8972847784564451230967345 6729635838423338423225509)
        ·
          refine ⟨1261806719704375954354783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6729635838423338423225509 1261806719704375954354783)
          ·
            refine ⟨1892710079556563931532175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261806719704375954354783 1892710079556563931532175)
            ·
              refine ⟨2839065119334845897298263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892710079556563931532175 2839065119334845897298263)
              ·
                refine ⟨4258597679002268845947395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839065119334845897298263 4258597679002268845947395)
                ·
                  refine ⟨6387896518503403268921093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258597679002268845947395 6387896518503403268921093)
                  ·
                    refine ⟨1197730597219388112922705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387896518503403268921093 1197730597219388112922705)
                    ·
                      refine ⟨898297947914541084692029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197730597219388112922705 898297947914541084692029)
                      ·
                        rfl

theorem cell23_1749429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_1749429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749429 prefixEnd_1749429 := by exact prefixLift 1749429
  have htrace : WordTrace (prefixWord ++ tailWord_1749429) baseStart_1749429 baseEnd_1749429 := by
    simpa [prefixWord, tailWord_1749429, baseEnd_1749429] using wordTrace_append hprefix tailTrace_1749429
  have hstable : (prefixWord ++ tailWord_1749429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749429).length < 2 ^ (prefixWord ++ tailWord_1749429).sum := by decide
  have hdescent : baseEnd_1749429 < baseStart_1749429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749431 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 1, 7]
def baseStart_1749431 : Nat := 118140960795 + 1749431 * 2 ^ 59
def prefixEnd_1749431 : Nat := 4983230072969 + 3 ^ 40 * 1749431 * 2
def baseEnd_1749431 : Nat := 299432991625283358955673

theorem tailTrace_1749431 : CollatzResearch.WordTrace tailWord_1749431 prefixEnd_1749431 299432991625283358955673 := by
  unfold tailWord_1749431
  simp only [CollatzResearch.WordTrace]
  refine ⟨63806990525117740872896147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42537993683411827248597431 63806990525117740872896147)
  ·
    refine ⟨95710485787676611309344221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63806990525117740872896147 95710485787676611309344221)
    ·
      refine ⟨35891432170378729241004083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95710485787676611309344221 35891432170378729241004083)
      ·
        refine ⟨53837148255568093861506125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35891432170378729241004083 53837148255568093861506125)
        ·
          refine ⟨20188930595838035198064797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53837148255568093861506125 20188930595838035198064797)
          ·
            refine ⟨7570848973439263199274299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20188930595838035198064797 7570848973439263199274299)
            ·
              refine ⟨11356273460158894798911449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570848973439263199274299 11356273460158894798911449)
              ·
                refine ⟨8517205095119171099183587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11356273460158894798911449 8517205095119171099183587)
                ·
                  refine ⟨12775807642678756648775381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8517205095119171099183587 12775807642678756648775381)
                  ·
                    refine ⟨299432991625283358955673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12775807642678756648775381 299432991625283358955673)
                    ·
                      rfl

theorem cell23_1749431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_1749431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749431 prefixEnd_1749431 := by exact prefixLift 1749431
  have htrace : WordTrace (prefixWord ++ tailWord_1749431) baseStart_1749431 baseEnd_1749431 := by
    simpa [prefixWord, tailWord_1749431, baseEnd_1749431] using wordTrace_append hprefix tailTrace_1749431
  have hstable : (prefixWord ++ tailWord_1749431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749431).length < 2 ^ (prefixWord ++ tailWord_1749431).sum := by decide
  have hdescent : baseEnd_1749431 < baseStart_1749431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749452 : List Nat := [2, 2, 1, 4, 3, 2, 1, 3, 5]
def baseStart_1749452 : Nat := 118140960795 + 1749452 * 2 ^ 59
def prefixEnd_1749452 : Nat := 4983230072969 + 3 ^ 40 * 1749452 * 2
def baseEnd_1749452 : Nat := 99812195329954943856047

theorem tailTrace_1749452 : CollatzResearch.WordTrace tailWord_1749452 prefixEnd_1749452 99812195329954943856047 := by
  unfold tailWord_1749452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903878229020830729705305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42538504305361107639607073 31903878229020830729705305)
  ·
    refine ⟨23927908671765623047278979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31903878229020830729705305 23927908671765623047278979)
    ·
      refine ⟨35891863007648434570918469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23927908671765623047278979 35891863007648434570918469)
      ·
        refine ⟨6729724313934081482047213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35891863007648434570918469 6729724313934081482047213)
        ·
          refine ⟨2523646617725280555767705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6729724313934081482047213 2523646617725280555767705)
          ·
            refine ⟨1892734963293960416825779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2523646617725280555767705 1892734963293960416825779)
            ·
              refine ⟨2839102444940940625238669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892734963293960416825779 2839102444940940625238669)
              ·
                refine ⟨1064663416852852734464501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2839102444940940625238669 1064663416852852734464501)
                ·
                  refine ⟨99812195329954943856047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1064663416852852734464501 99812195329954943856047)
                  ·
                    rfl

theorem cell23_1749452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_1749452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749452 prefixEnd_1749452 := by exact prefixLift 1749452
  have htrace : WordTrace (prefixWord ++ tailWord_1749452) baseStart_1749452 baseEnd_1749452 := by
    simpa [prefixWord, tailWord_1749452, baseEnd_1749452] using wordTrace_append hprefix tailTrace_1749452
  have hstable : (prefixWord ++ tailWord_1749452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749452).length < 2 ^ (prefixWord ++ tailWord_1749452).sum := by decide
  have hdescent : baseEnd_1749452 < baseStart_1749452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749481 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_1749481 : Nat := 118140960795 + 1749481 * 2 ^ 59
def prefixEnd_1749481 : Nat := 4983230072969 + 3 ^ 40 * 1749481 * 2
def baseEnd_1749481 : Nat := 898324648908574881241789

theorem tailTrace_1749481 : CollatzResearch.WordTrace tailWord_1749481 prefixEnd_1749481 898324648908574881241789 := by
  unfold tailWord_1749481
  simp only [CollatzResearch.WordTrace]
  refine ⟨63808814174936599412216297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42539209449957732941477531 63808814174936599412216297)
  ·
    refine ⟨47856610631202449559162223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63808814174936599412216297 47856610631202449559162223)
    ·
      refine ⟨71784915946803674338743335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47856610631202449559162223 71784915946803674338743335)
      ·
        refine ⟨107677373920205511508115003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71784915946803674338743335 107677373920205511508115003)
        ·
          refine ⟨161516060880308267262172505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107677373920205511508115003 161516060880308267262172505)
          ·
            refine ⟨121137045660231200446629379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161516060880308267262172505 121137045660231200446629379)
            ·
              refine ⟨181705568490346800669944069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121137045660231200446629379 181705568490346800669944069)
              ·
                refine ⟨34069794091940025125614513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181705568490346800669944069 34069794091940025125614513)
                ·
                  refine ⟨25552345568955018844210885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34069794091940025125614513 25552345568955018844210885)
                  ·
                    refine ⟨4791064794179066033289541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25552345568955018844210885 4791064794179066033289541)
                    ·
                      refine ⟨898324648908574881241789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4791064794179066033289541 898324648908574881241789)
                      ·
                        rfl

theorem cell23_1749481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_1749481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749481 prefixEnd_1749481 := by exact prefixLift 1749481
  have htrace : WordTrace (prefixWord ++ tailWord_1749481) baseStart_1749481 baseEnd_1749481 := by
    simpa [prefixWord, tailWord_1749481, baseEnd_1749481] using wordTrace_append hprefix tailTrace_1749481
  have hstable : (prefixWord ++ tailWord_1749481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749481).length < 2 ^ (prefixWord ++ tailWord_1749481).sum := by decide
  have hdescent : baseEnd_1749481 < baseStart_1749481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749488 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3]
def baseStart_1749488 : Nat := 118140960795 + 1749488 * 2 ^ 59
def prefixEnd_1749488 : Nat := 4983230072969 + 3 ^ 40 * 1749488 * 2
def baseEnd_1749488 : Nat := 898328243273156353854257

theorem tailTrace_1749488 : CollatzResearch.WordTrace tailWord_1749488 prefixEnd_1749488 898328243273156353854257 := by
  unfold tailWord_1749488
  simp only [CollatzResearch.WordTrace]
  refine ⟨31904534742955619803860559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42539379657274159738480745 31904534742955619803860559)
  ·
    refine ⟨47856802114433429705790839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31904534742955619803860559 47856802114433429705790839)
    ·
      refine ⟨71785203171650144558686259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47856802114433429705790839 71785203171650144558686259)
      ·
        refine ⟨107677804757475216838029389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71785203171650144558686259 107677804757475216838029389)
        ·
          refine ⟨40379176784053206314261021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107677804757475216838029389 40379176784053206314261021)
          ·
            refine ⟨15142191294019952367847883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40379176784053206314261021 15142191294019952367847883)
            ·
              refine ⟨22713286941029928551771825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15142191294019952367847883 22713286941029928551771825)
              ·
                refine ⟨17034965205772446413828869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22713286941029928551771825 17034965205772446413828869)
                ·
                  refine ⟨3194055976082333702592913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17034965205772446413828869 3194055976082333702592913)
                  ·
                    refine ⟨2395541982061750276944685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3194055976082333702592913 2395541982061750276944685)
                    ·
                      refine ⟨898328243273156353854257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395541982061750276944685 898328243273156353854257)
                      ·
                        rfl

theorem cell23_1749488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_1749488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749488 prefixEnd_1749488 := by exact prefixLift 1749488
  have htrace : WordTrace (prefixWord ++ tailWord_1749488) baseStart_1749488 baseEnd_1749488 := by
    simpa [prefixWord, tailWord_1749488, baseEnd_1749488] using wordTrace_append hprefix tailTrace_1749488
  have hstable : (prefixWord ++ tailWord_1749488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749488).length < 2 ^ (prefixWord ++ tailWord_1749488).sum := by decide
  have hdescent : baseEnd_1749488 < baseStart_1749488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749505 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1749505 : Nat := 118140960795 + 1749505 * 2 ^ 59
def prefixEnd_1749505 : Nat := 4983230072969 + 3 ^ 40 * 1749505 * 2
def baseEnd_1749505 : Nat := 898336972444282787341679

theorem tailTrace_1749505 : CollatzResearch.WordTrace tailWord_1749505 prefixEnd_1749505 898336972444282787341679 := by
  unfold tailWord_1749505
  simp only [CollatzResearch.WordTrace]
  refine ⟨63809689526849651511089969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42539793017899767674059979 63809689526849651511089969)
  ·
    refine ⟨47857267145137238633317477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63809689526849651511089969 47857267145137238633317477)
    ·
      refine ⟨8973237589713232243747027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47857267145137238633317477 8973237589713232243747027)
      ·
        refine ⟨13459856384569848365620541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8973237589713232243747027 13459856384569848365620541)
        ·
          refine ⟨5047446144213693137107703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13459856384569848365620541 5047446144213693137107703)
          ·
            refine ⟨7571169216320539705661555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047446144213693137107703 7571169216320539705661555)
            ·
              refine ⟨11356753824480809558492333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571169216320539705661555 11356753824480809558492333)
              ·
                refine ⟨4258782684180303584434625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11356753824480809558492333 4258782684180303584434625)
                ·
                  refine ⟨3194087013135227688325969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258782684180303584434625 3194087013135227688325969)
                  ·
                    refine ⟨2395565259851420766244477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3194087013135227688325969 2395565259851420766244477)
                    ·
                      refine ⟨898336972444282787341679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395565259851420766244477 898336972444282787341679)
                      ·
                        rfl

theorem cell23_1749505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1749505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749505 prefixEnd_1749505 := by exact prefixLift 1749505
  have htrace : WordTrace (prefixWord ++ tailWord_1749505) baseStart_1749505 baseEnd_1749505 := by
    simpa [prefixWord, tailWord_1749505, baseEnd_1749505] using wordTrace_append hprefix tailTrace_1749505
  have hstable : (prefixWord ++ tailWord_1749505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749505).length < 2 ^ (prefixWord ++ tailWord_1749505).sum := by decide
  have hdescent : baseEnd_1749505 < baseStart_1749505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749531 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5]
def baseStart_1749531 : Nat := 118140960795 + 1749531 * 2 ^ 59
def prefixEnd_1749531 : Nat := 4983230072969 + 3 ^ 40 * 1749531 * 2
def baseEnd_1749531 : Nat := 898350322941299685616559

theorem tailTrace_1749531 : CollatzResearch.WordTrace tailWord_1749531 prefixEnd_1749531 898350322941299685616559 := by
  unfold tailWord_1749531
  simp only [CollatzResearch.WordTrace]
  refine ⟨63810637824755457951536447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42540425216503638634357631 63810637824755457951536447)
  ·
    refine ⟨95715956737133186927304671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63810637824755457951536447 95715956737133186927304671)
    ·
      refine ⟨143573935105699780390957007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95715956737133186927304671 143573935105699780390957007)
      ·
        refine ⟨215360902658549670586435511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143573935105699780390957007 215360902658549670586435511)
        ·
          refine ⟨323041353987824505879653267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215360902658549670586435511 323041353987824505879653267)
          ·
            refine ⟨484562030981736758819479901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323041353987824505879653267 484562030981736758819479901)
            ·
              refine ⟨181710761618151284557304963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484562030981736758819479901 181710761618151284557304963)
              ·
                refine ⟨272566142427226926835957445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181710761618151284557304963 272566142427226926835957445)
                ·
                  refine ⟨51106151705105048781742021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272566142427226926835957445 51106151705105048781742021)
                  ·
                    refine ⟨9582403444707196646576629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51106151705105048781742021 9582403444707196646576629)
                    ·
                      refine ⟨898350322941299685616559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9582403444707196646576629 898350322941299685616559)
                      ·
                        rfl

theorem cell23_1749531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_1749531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749531 prefixEnd_1749531 := by exact prefixLift 1749531
  have htrace : WordTrace (prefixWord ++ tailWord_1749531) baseStart_1749531 baseEnd_1749531 := by
    simpa [prefixWord, tailWord_1749531, baseEnd_1749531] using wordTrace_append hprefix tailTrace_1749531
  have hstable : (prefixWord ++ tailWord_1749531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749531).length < 2 ^ (prefixWord ++ tailWord_1749531).sum := by decide
  have hdescent : baseEnd_1749531 < baseStart_1749531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749535 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 3]
def baseStart_1749535 : Nat := 118140960795 + 1749535 * 2 ^ 59
def prefixEnd_1749535 : Nat := 4983230072969 + 3 ^ 40 * 1749535 * 2
def baseEnd_1749535 : Nat := 898352376863917669966541

theorem tailTrace_1749535 : CollatzResearch.WordTrace tailWord_1749535 prefixEnd_1749535 898352376863917669966541 := by
  unfold tailWord_1749535
  simp only [CollatzResearch.WordTrace]
  refine ⟨63810783716740966634682059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42540522477827311089788039 63810783716740966634682059)
  ·
    refine ⟨95716175575111449952023089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63810783716740966634682059 95716175575111449952023089)
    ·
      refine ⟨71787131681333587464017317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95716175575111449952023089 71787131681333587464017317)
      ·
        refine ⟨13460087190250047649503247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71787131681333587464017317 13460087190250047649503247)
        ·
          refine ⟨20190130785375071474254871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13460087190250047649503247 20190130785375071474254871)
          ·
            refine ⟨30285196178062607211382307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20190130785375071474254871 30285196178062607211382307)
            ·
              refine ⟨45427794267093910817073461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30285196178062607211382307 45427794267093910817073461)
              ·
                refine ⟨4258855712540054139100637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45427794267093910817073461 4258855712540054139100637)
                ·
                  refine ⟨1597070892202520302162739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4258855712540054139100637 1597070892202520302162739)
                  ·
                    refine ⟨2395606338303780453244109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597070892202520302162739 2395606338303780453244109)
                    ·
                      refine ⟨898352376863917669966541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395606338303780453244109 898352376863917669966541)
                      ·
                        rfl

theorem cell23_1749535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_1749535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749535 prefixEnd_1749535 := by exact prefixLift 1749535
  have htrace : WordTrace (prefixWord ++ tailWord_1749535) baseStart_1749535 baseEnd_1749535 := by
    simpa [prefixWord, tailWord_1749535, baseEnd_1749535] using wordTrace_append hprefix tailTrace_1749535
  have hstable : (prefixWord ++ tailWord_1749535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749535).length < 2 ^ (prefixWord ++ tailWord_1749535).sum := by decide
  have hdescent : baseEnd_1749535 < baseStart_1749535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749556 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1749556 : Nat := 118140960795 + 1749556 * 2 ^ 59
def prefixEnd_1749556 : Nat := 4983230072969 + 3 ^ 40 * 1749556 * 2
def baseEnd_1749556 : Nat := 898363159957662087803945

theorem tailTrace_1749556 : CollatzResearch.WordTrace tailWord_1749556 prefixEnd_1749556 898363159957662087803945 := by
  unfold tailWord_1749556
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905774824832443610598261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42541033099776591480797681 31905774824832443610598261)
  ·
    refine ⟨2991166389828041588493587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31905774824832443610598261 2991166389828041588493587)
    ·
      refine ⟨4486749584742062382740381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991166389828041588493587 4486749584742062382740381)
      ·
        refine ⟨1682531094278273393527643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4486749584742062382740381 1682531094278273393527643)
        ·
          refine ⟨2523796641417410090291465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682531094278273393527643 2523796641417410090291465)
          ·
            refine ⟨1892847481063057567718599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2523796641417410090291465 1892847481063057567718599)
            ·
              refine ⟨2839271221594586351577899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892847481063057567718599 2839271221594586351577899)
              ·
                refine ⟨4258906832391879527366849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839271221594586351577899 4258906832391879527366849)
                ·
                  refine ⟨3194180124293909645525137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258906832391879527366849 3194180124293909645525137)
                  ·
                    refine ⟨2395635093220432234143853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3194180124293909645525137 2395635093220432234143853)
                    ·
                      refine ⟨898363159957662087803945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395635093220432234143853 898363159957662087803945)
                      ·
                        rfl

theorem cell23_1749556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1749556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749556 prefixEnd_1749556 := by exact prefixLift 1749556
  have htrace : WordTrace (prefixWord ++ tailWord_1749556) baseStart_1749556 baseEnd_1749556 := by
    simpa [prefixWord, tailWord_1749556, baseEnd_1749556] using wordTrace_append hprefix tailTrace_1749556
  have hstable : (prefixWord ++ tailWord_1749556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749556).length < 2 ^ (prefixWord ++ tailWord_1749556).sum := by decide
  have hdescent : baseEnd_1749556 < baseStart_1749556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749562 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2]
def baseStart_1749562 : Nat := 118140960795 + 1749562 * 2 ^ 59
def prefixEnd_1749562 : Nat := 4983230072969 + 3 ^ 40 * 1749562 * 2
def baseEnd_1749562 : Nat := 898366240841589064328917

theorem tailTrace_1749562 : CollatzResearch.WordTrace tailWord_1749562 prefixEnd_1749562 898366240841589064328917 := by
  unfold tailWord_1749562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952942121910787561478735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42541178991762100163943293 15952942121910787561478735)
  ·
    refine ⟨23929413182866181342218103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15952942121910787561478735 23929413182866181342218103)
    ·
      refine ⟨35894119774299272013327155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23929413182866181342218103 35894119774299272013327155)
      ·
        refine ⟨53841179661448908019990733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35894119774299272013327155 53841179661448908019990733)
        ·
          refine ⟨20190442373043340507496525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53841179661448908019990733 20190442373043340507496525)
          ·
            refine ⟨7571415889891252690311197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20190442373043340507496525 7571415889891252690311197)
            ·
              refine ⟨2839280958709219758866699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7571415889891252690311197 2839280958709219758866699)
              ·
                refine ⟨4258921438063829638300049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839280958709219758866699 4258921438063829638300049)
                ·
                  refine ⟨3194191078547872228725037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258921438063829638300049 3194191078547872228725037)
                  ·
                    refine ⟨1197821654455452085771889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194191078547872228725037 1197821654455452085771889)
                    ·
                      refine ⟨898366240841589064328917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197821654455452085771889 898366240841589064328917)
                      ·
                        rfl

theorem cell23_1749562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_1749562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749562 prefixEnd_1749562 := by exact prefixLift 1749562
  have htrace : WordTrace (prefixWord ++ tailWord_1749562) baseStart_1749562 baseEnd_1749562 := by
    simpa [prefixWord, tailWord_1749562, baseEnd_1749562] using wordTrace_append hprefix tailTrace_1749562
  have hstable : (prefixWord ++ tailWord_1749562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749562).length < 2 ^ (prefixWord ++ tailWord_1749562).sum := by decide
  have hdescent : baseEnd_1749562 < baseStart_1749562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749568 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 1, 6]
def baseStart_1749568 : Nat := 118140960795 + 1749568 * 2 ^ 59
def prefixEnd_1749568 : Nat := 4983230072969 + 3 ^ 40 * 1749568 * 2
def baseEnd_1749568 : Nat := 299456440575172013617963

theorem tailTrace_1749568 : CollatzResearch.WordTrace tailWord_1749568 prefixEnd_1749568 299456440575172013617963 := by
  unfold tailWord_1749568
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905993662810706635316679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42541324883747608847088905 31905993662810706635316679)
  ·
    refine ⟨47858990494216059952975019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31905993662810706635316679 47858990494216059952975019)
    ·
      refine ⟨71788485741324089929462529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47858990494216059952975019 71788485741324089929462529)
      ·
        refine ⟨53841364305993067447096897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71788485741324089929462529 53841364305993067447096897)
        ·
          refine ⟨40381023229494800585322673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53841364305993067447096897 40381023229494800585322673)
          ·
            refine ⟨30285767422121100438992005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40381023229494800585322673 30285767422121100438992005)
            ·
              refine ⟨5678581391647706332311001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30285767422121100438992005 5678581391647706332311001)
              ·
                refine ⟨4258936043735779749233251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678581391647706332311001 4258936043735779749233251)
                ·
                  refine ⟨6388404065603669623849877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258936043735779749233251 6388404065603669623849877)
                  ·
                    refine ⟨299456440575172013617963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6388404065603669623849877 299456440575172013617963)
                    ·
                      rfl

theorem cell23_1749568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_1749568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749568 prefixEnd_1749568 := by exact prefixLift 1749568
  have htrace : WordTrace (prefixWord ++ tailWord_1749568) baseStart_1749568 baseEnd_1749568 := by
    simpa [prefixWord, tailWord_1749568, baseEnd_1749568] using wordTrace_append hprefix tailTrace_1749568
  have hstable : (prefixWord ++ tailWord_1749568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749568).length < 2 ^ (prefixWord ++ tailWord_1749568).sum := by decide
  have hdescent : baseEnd_1749568 < baseStart_1749568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749569 : List Nat := [1, 2, 5, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_1749569 : Nat := 118140960795 + 1749569 * 2 ^ 59
def prefixEnd_1749569 : Nat := 4983230072969 + 3 ^ 40 * 1749569 * 2
def baseEnd_1749569 : Nat := 898369835206170536941385

theorem tailTrace_1749569 : CollatzResearch.WordTrace tailWord_1749569 prefixEnd_1749569 898369835206170536941385 := by
  unfold tailWord_1749569
  simp only [CollatzResearch.WordTrace]
  refine ⟨63812023798617790441419761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42541349199078526960946507 63812023798617790441419761)
  ·
    refine ⟨47859017848963342831064821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63812023798617790441419761 47859017848963342831064821)
    ·
      refine ⟨4486782923340313390412327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47859017848963342831064821 4486782923340313390412327)
      ·
        refine ⟨6730174385010470085618491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486782923340313390412327 6730174385010470085618491)
        ·
          refine ⟨10095261577515705128427737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6730174385010470085618491 10095261577515705128427737)
          ·
            refine ⟨7571446183136778846320803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10095261577515705128427737 7571446183136778846320803)
            ·
              refine ⟨11357169274705168269481205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571446183136778846320803 11357169274705168269481205)
              ·
                refine ⟨1064734619503609525263863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11357169274705168269481205 1064734619503609525263863)
                ·
                  refine ⟨1597101929255414287895795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064734619503609525263863 1597101929255414287895795)
                  ·
                    refine ⟨2395652893883121431843693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597101929255414287895795 2395652893883121431843693)
                    ·
                      refine ⟨898369835206170536941385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395652893883121431843693 898369835206170536941385)
                      ·
                        rfl

theorem cell23_1749569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_1749569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749569 prefixEnd_1749569 := by exact prefixLift 1749569
  have htrace : WordTrace (prefixWord ++ tailWord_1749569) baseStart_1749569 baseEnd_1749569 := by
    simpa [prefixWord, tailWord_1749569, baseEnd_1749569] using wordTrace_append hprefix tailTrace_1749569
  have hstable : (prefixWord ++ tailWord_1749569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749569).length < 2 ^ (prefixWord ++ tailWord_1749569).sum := by decide
  have hdescent : baseEnd_1749569 < baseStart_1749569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749585 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 4, 4]
def baseStart_1749585 : Nat := 118140960795 + 1749585 * 2 ^ 59
def prefixEnd_1749585 : Nat := 4983230072969 + 3 ^ 40 * 1749585 * 2
def baseEnd_1749585 : Nat := 299459350298880824780437

theorem tailTrace_1749585 : CollatzResearch.WordTrace tailWord_1749585 prefixEnd_1749585 299459350298880824780437 := by
  unfold tailWord_1749585
  simp only [CollatzResearch.WordTrace]
  refine ⟨63812607366559825174002209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42541738244373216782668139 63812607366559825174002209)
  ·
    refine ⟨47859455524919868880501657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63812607366559825174002209 47859455524919868880501657)
    ·
      refine ⟨35894591643689901660376243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47859455524919868880501657 35894591643689901660376243)
      ·
        refine ⟨53841887465534852490564365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35894591643689901660376243 53841887465534852490564365)
        ·
          refine ⟨20190707799575569683961637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53841887465534852490564365 20190707799575569683961637)
          ·
            refine ⟨3785757712420419315742807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20190707799575569683961637 3785757712420419315742807)
            ·
              refine ⟨5678636568630628973614211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785757712420419315742807 5678636568630628973614211)
              ·
                refine ⟨8517954852945943460421317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678636568630628973614211 8517954852945943460421317)
                ·
                  refine ⟨1597116534927364398828997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8517954852945943460421317 1597116534927364398828997)
                  ·
                    refine ⟨299459350298880824780437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597116534927364398828997 299459350298880824780437)
                    ·
                      rfl

theorem cell23_1749585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_1749585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749585 prefixEnd_1749585 := by exact prefixLift 1749585
  have htrace : WordTrace (prefixWord ++ tailWord_1749585) baseStart_1749585 baseEnd_1749585 := by
    simpa [prefixWord, tailWord_1749585, baseEnd_1749585] using wordTrace_append hprefix tailTrace_1749585
  have hstable : (prefixWord ++ tailWord_1749585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749585).length < 2 ^ (prefixWord ++ tailWord_1749585).sum := by decide
  have hdescent : baseEnd_1749585 < baseStart_1749585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749592 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 3, 2, 2]
def baseStart_1749592 : Nat := 118140960795 + 1749592 * 2 ^ 59
def prefixEnd_1749592 : Nat := 4983230072969 + 3 ^ 40 * 1749592 * 2
def baseEnd_1749592 : Nat := 898381645261223946953779

theorem tailTrace_1749592 : CollatzResearch.WordTrace tailWord_1749592 prefixEnd_1749592 898381645261223946953779 := by
  unfold tailWord_1749592
  simp only [CollatzResearch.WordTrace]
  refine ⟨31906431338767232684753515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42541908451689643579671353 31906431338767232684753515)
  ·
    refine ⟨47859647008150849027130273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31906431338767232684753515 47859647008150849027130273)
    ·
      refine ⟨35894735256113136770347705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47859647008150849027130273 35894735256113136770347705)
      ·
        refine ⟨26921051442084852577760779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35894735256113136770347705 26921051442084852577760779)
        ·
          refine ⟨40381577163127278866641169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26921051442084852577760779 40381577163127278866641169)
          ·
            refine ⟨30286182872345459149980877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40381577163127278866641169 30286182872345459149980877)
            ·
              refine ⟨11357318577129547181242829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30286182872345459149980877 11357318577129547181242829)
              ·
                refine ⟨4258994466423580192966061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11357318577129547181242829 4258994466423580192966061)
                ·
                  refine ⟨1597122924908842572362273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4258994466423580192966061 1597122924908842572362273)
                  ·
                    refine ⟨1197842193681631929271705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1597122924908842572362273 1197842193681631929271705)
                    ·
                      refine ⟨898381645261223946953779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197842193681631929271705 898381645261223946953779)
                      ·
                        rfl

theorem cell23_1749592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_1749592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749592 prefixEnd_1749592 := by exact prefixLift 1749592
  have htrace : WordTrace (prefixWord ++ tailWord_1749592) baseStart_1749592 baseEnd_1749592 := by
    simpa [prefixWord, tailWord_1749592, baseEnd_1749592] using wordTrace_append hprefix tailTrace_1749592
  have hstable : (prefixWord ++ tailWord_1749592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749592).length < 2 ^ (prefixWord ++ tailWord_1749592).sum := by decide
  have hdescent : baseEnd_1749592 < baseStart_1749592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749605 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1749605 : Nat := 118140960795 + 1749605 * 2 ^ 59
def prefixEnd_1749605 : Nat := 4983230072969 + 3 ^ 40 * 1749605 * 2
def baseEnd_1749605 : Nat := 898388320509732396091219

theorem tailTrace_1749605 : CollatzResearch.WordTrace tailWord_1749605 prefixEnd_1749605 898388320509732396091219 := by
  unfold tailWord_1749605
  simp only [CollatzResearch.WordTrace]
  refine ⟨63813336826487368589730269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42542224550991579059820179 63813336826487368589730269)
  ·
    refine ⟨23930001309932763221148851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63813336826487368589730269 23930001309932763221148851)
    ·
      refine ⟨35895001964899144831723277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23930001309932763221148851 35895001964899144831723277)
      ·
        refine ⟨13460625736837179311896229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35895001964899144831723277 13460625736837179311896229)
        ·
          refine ⟨2523867325656971120980543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13460625736837179311896229 2523867325656971120980543)
          ·
            refine ⟨3785800988485456681470815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523867325656971120980543 3785800988485456681470815)
            ·
              refine ⟨5678701482728185022206223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785800988485456681470815 5678701482728185022206223)
              ·
                refine ⟨8518052224092277533309335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678701482728185022206223 8518052224092277533309335)
                ·
                  refine ⟨12777078336138416299964003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8518052224092277533309335 12777078336138416299964003)
                  ·
                    refine ⟨19165617504207624449946005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12777078336138416299964003 19165617504207624449946005)
                    ·
                      refine ⟨898388320509732396091219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19165617504207624449946005 898388320509732396091219)
                      ·
                        rfl

theorem cell23_1749605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1749605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749605 prefixEnd_1749605 := by exact prefixLift 1749605
  have htrace : WordTrace (prefixWord ++ tailWord_1749605) baseStart_1749605 baseEnd_1749605 := by
    simpa [prefixWord, tailWord_1749605, baseEnd_1749605] using wordTrace_append hprefix tailTrace_1749605
  have hstable : (prefixWord ++ tailWord_1749605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749605).length < 2 ^ (prefixWord ++ tailWord_1749605).sum := by decide
  have hdescent : baseEnd_1749605 < baseStart_1749605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749709 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1749709 : Nat := 118140960795 + 1749709 * 2 ^ 59
def prefixEnd_1749709 : Nat := 4983230072969 + 3 ^ 40 * 1749709 * 2
def baseEnd_1749709 : Nat := 299480574165933329730247

theorem tailTrace_1749709 : CollatzResearch.WordTrace tailWord_1749709 prefixEnd_1749709 299480574165933329730247 := by
  unfold tailWord_1749709
  simp only [CollatzResearch.WordTrace]
  refine ⟨63817130018110594351516181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42544753345407062901010787 63817130018110594351516181)
  ·
    refine ⟨2991427969598934110227321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63817130018110594351516181 2991427969598934110227321)
    ·
      refine ⟨2243570977199200582670491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2991427969598934110227321 2243570977199200582670491)
      ·
        refine ⟨3365356465798800874005737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243570977199200582670491 3365356465798800874005737)
        ·
          refine ⟨2524017349349100655504303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3365356465798800874005737 2524017349349100655504303)
          ·
            refine ⟨3786026024023650983256455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524017349349100655504303 3786026024023650983256455)
            ·
              refine ⟨5679039036035476474884683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786026024023650983256455 5679039036035476474884683)
              ·
                refine ⟨8518558554053214712327025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679039036035476474884683 8518558554053214712327025)
                ·
                  refine ⟨6388918915539911034245269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8518558554053214712327025 6388918915539911034245269)
                  ·
                    refine ⟨299480574165933329730247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6388918915539911034245269 299480574165933329730247)
                    ·
                      rfl

theorem cell23_1749709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1749709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749709 prefixEnd_1749709 := by exact prefixLift 1749709
  have htrace : WordTrace (prefixWord ++ tailWord_1749709) baseStart_1749709 baseEnd_1749709 := by
    simpa [prefixWord, tailWord_1749709, baseEnd_1749709] using wordTrace_append hprefix tailTrace_1749709
  have hstable : (prefixWord ++ tailWord_1749709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749709).length < 2 ^ (prefixWord ++ tailWord_1749709).sum := by decide
  have hdescent : baseEnd_1749709 < baseStart_1749709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749716 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1749716 : Nat := 118140960795 + 1749716 * 2 ^ 59
def prefixEnd_1749716 : Nat := 4983230072969 + 3 ^ 40 * 1749716 * 2
def baseEnd_1749716 : Nat := 898445316862381461803209

theorem tailTrace_1749716 : CollatzResearch.WordTrace tailWord_1749716 prefixEnd_1749716 898445316862381461803209 := by
  unfold tailWord_1749716
  simp only [CollatzResearch.WordTrace]
  refine ⟨31908692664542617273510501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42544923552723489698014001 31908692664542617273510501)
  ·
    refine ⟨5982879874601740738783219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31908692664542617273510501 5982879874601740738783219)
    ·
      refine ⟨8974319811902611108174829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5982879874601740738783219 8974319811902611108174829)
      ·
        refine ⟨3365369929463479165565561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8974319811902611108174829 3365369929463479165565561)
        ·
          refine ⟨2524027447097609374174171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3365369929463479165565561 2524027447097609374174171)
          ·
            refine ⟨3786041170646414061261257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524027447097609374174171 3786041170646414061261257)
            ·
              refine ⟨2839530877984810545945943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3786041170646414061261257 2839530877984810545945943)
              ·
                refine ⟨4259296316977215818918915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839530877984810545945943 4259296316977215818918915)
                ·
                  refine ⟨6388944475465823728378373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259296316977215818918915 6388944475465823728378373)
                  ·
                    refine ⟨1197927089149841949070945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6388944475465823728378373 1197927089149841949070945)
                    ·
                      refine ⟨898445316862381461803209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1197927089149841949070945 898445316862381461803209)
                      ·
                        rfl

theorem cell23_1749716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1749716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749716 prefixEnd_1749716 := by exact prefixLift 1749716
  have htrace : WordTrace (prefixWord ++ tailWord_1749716) baseStart_1749716 baseEnd_1749716 := by
    simpa [prefixWord, tailWord_1749716, baseEnd_1749716] using wordTrace_append hprefix tailTrace_1749716
  have hstable : (prefixWord ++ tailWord_1749716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749716).length < 2 ^ (prefixWord ++ tailWord_1749716).sum := by decide
  have hdescent : baseEnd_1749716 < baseStart_1749716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749775 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 3]
def baseStart_1749775 : Nat := 118140960795 + 1749775 * 2 ^ 59
def prefixEnd_1749775 : Nat := 4983230072969 + 3 ^ 40 * 1749775 * 2
def baseEnd_1749775 : Nat := 898475612220996730965437

theorem tailTrace_1749775 : CollatzResearch.WordTrace tailWord_1749775 prefixEnd_1749775 898475612220996730965437 := by
  unfold tailWord_1749775
  simp only [CollatzResearch.WordTrace]
  refine ⟨63819537235871487623418779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42546358157247658415612519 63819537235871487623418779)
  ·
    refine ⟨95729305853807231435128169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63819537235871487623418779 95729305853807231435128169)
    ·
      refine ⟨71796979390355423576346127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95729305853807231435128169 71796979390355423576346127)
      ·
        refine ⟨107695469085533135364519191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71796979390355423576346127 107695469085533135364519191)
        ·
          refine ⟨161543203628299703046778787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107695469085533135364519191 161543203628299703046778787)
          ·
            refine ⟨242314805442449554570168181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161543203628299703046778787 242314805442449554570168181)
            ·
              refine ⟨22717013010229645740953267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242314805442449554570168181 22717013010229645740953267)
              ·
                refine ⟨34075519515344468611429901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22717013010229645740953267 34075519515344468611429901)
                ·
                  refine ⟨12778319818254175729286213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34075519515344468611429901 12778319818254175729286213)
                  ·
                    refine ⟨2395934965922657949241165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12778319818254175729286213 2395934965922657949241165)
                    ·
                      refine ⟨898475612220996730965437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395934965922657949241165 898475612220996730965437)
                      ·
                        rfl

theorem cell23_1749775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_1749775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749775 prefixEnd_1749775 := by exact prefixLift 1749775
  have htrace : WordTrace (prefixWord ++ tailWord_1749775) baseStart_1749775 baseEnd_1749775 := by
    simpa [prefixWord, tailWord_1749775, baseEnd_1749775] using wordTrace_append hprefix tailTrace_1749775
  have hstable : (prefixWord ++ tailWord_1749775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749775).length < 2 ^ (prefixWord ++ tailWord_1749775).sum := by decide
  have hdescent : baseEnd_1749775 < baseStart_1749775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749792 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1749792 : Nat := 118140960795 + 1749792 * 2 ^ 59
def prefixEnd_1749792 : Nat := 4983230072969 + 3 ^ 40 * 1749792 * 2
def baseEnd_1749792 : Nat := 898484341392123164452859

theorem tailTrace_1749792 : CollatzResearch.WordTrace tailWord_1749792 prefixEnd_1749792 898484341392123164452859 := by
  unfold tailWord_1749792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31910078638404949763393815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42546771517873266351191753 31910078638404949763393815)
  ·
    refine ⟨47865117957607424645090723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31910078638404949763393815 47865117957607424645090723)
    ·
      refine ⟨71797676936411136967636085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47865117957607424645090723 71797676936411136967636085)
      ·
        refine ⟨6731032212788544090715883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71797676936411136967636085 6731032212788544090715883)
        ·
          refine ⟨10096548319182816136073825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6731032212788544090715883 10096548319182816136073825)
          ·
            refine ⟨7572411239387112102055369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10096548319182816136073825 7572411239387112102055369)
            ·
              refine ⟨5679308429540334076541527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7572411239387112102055369 5679308429540334076541527)
              ·
                refine ⟨8518962644310501114812291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679308429540334076541527 8518962644310501114812291)
                ·
                  refine ⟨12778443966465751672218437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8518962644310501114812291 12778443966465751672218437)
                  ·
                    refine ⟨2395958243712328438540957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12778443966465751672218437 2395958243712328438540957)
                    ·
                      refine ⟨898484341392123164452859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2395958243712328438540957 898484341392123164452859)
                      ·
                        rfl

theorem cell23_1749792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1749792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749792 prefixEnd_1749792 := by exact prefixLift 1749792
  have htrace : WordTrace (prefixWord ++ tailWord_1749792) baseStart_1749792 baseEnd_1749792 := by
    simpa [prefixWord, tailWord_1749792, baseEnd_1749792] using wordTrace_append hprefix tailTrace_1749792
  have hstable : (prefixWord ++ tailWord_1749792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749792).length < 2 ^ (prefixWord ++ tailWord_1749792).sum := by decide
  have hdescent : baseEnd_1749792 < baseStart_1749792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749816 : List Nat := [2, 1, 2, 1, 3, 2, 5, 2, 1, 4]
def baseStart_1749816 : Nat := 118140960795 + 1749816 * 2 ^ 59
def prefixEnd_1749816 : Nat := 4983230072969 + 3 ^ 40 * 1749816 * 2
def baseEnd_1749816 : Nat := 299498888309277023517583

theorem tailTrace_1749816 : CollatzResearch.WordTrace tailWord_1749816 prefixEnd_1749816 299498888309277023517583 := by
  unfold tailWord_1749816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31910516314361475812830651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42547355085815301083774201 31910516314361475812830651)
  ·
    refine ⟨47865774471542213719245977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31910516314361475812830651 47865774471542213719245977)
    ·
      refine ⟨35899330853656660289434483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47865774471542213719245977 35899330853656660289434483)
      ·
        refine ⟨53848996280484990434151725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35899330853656660289434483 53848996280484990434151725)
        ·
          refine ⟨20193373605181871412806897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53848996280484990434151725 20193373605181871412806897)
          ·
            refine ⟨15145030203886403559605173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20193373605181871412806897 15145030203886403559605173)
            ·
              refine ⟨1419846581614350333712985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15145030203886403559605173 1419846581614350333712985)
              ·
                refine ⟨1064884936210762750284739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419846581614350333712985 1064884936210762750284739)
                ·
                  refine ⟨1597327404316144125427109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064884936210762750284739 1597327404316144125427109)
                  ·
                    refine ⟨299498888309277023517583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597327404316144125427109 299498888309277023517583)
                    ·
                      rfl

theorem cell23_1749816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_1749816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749816 prefixEnd_1749816 := by exact prefixLift 1749816
  have htrace : WordTrace (prefixWord ++ tailWord_1749816) baseStart_1749816 baseEnd_1749816 := by
    simpa [prefixWord, tailWord_1749816, baseEnd_1749816] using wordTrace_append hprefix tailTrace_1749816
  have hstable : (prefixWord ++ tailWord_1749816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749816).length < 2 ^ (prefixWord ++ tailWord_1749816).sum := by decide
  have hdescent : baseEnd_1749816 < baseStart_1749816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749842 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1749842 : Nat := 118140960795 + 1749842 * 2 ^ 59
def prefixEnd_1749842 : Nat := 4983230072969 + 3 ^ 40 * 1749842 * 2
def baseEnd_1749842 : Nat := 299503338474949322942543

theorem tailTrace_1749842 : CollatzResearch.WordTrace tailWord_1749842 prefixEnd_1749842 299503338474949322942543 := by
  unfold tailWord_1749842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955495231657189516526945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42547987284419172044071853 15955495231657189516526945)
  ·
    refine ⟨11966621423742892137395209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15955495231657189516526945 11966621423742892137395209)
    ·
      refine ⟨8974966067807169103046407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11966621423742892137395209 8974966067807169103046407)
      ·
        refine ⟨13462449101710753654569611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8974966067807169103046407 13462449101710753654569611)
        ·
          refine ⟨20193673652566130481854417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13462449101710753654569611 20193673652566130481854417)
          ·
            refine ⟨15145255239424597861390813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20193673652566130481854417 15145255239424597861390813)
            ·
              refine ⟨5679470714784224198021555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15145255239424597861390813 5679470714784224198021555)
              ·
                refine ⟨8519206072176336297032333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679470714784224198021555 8519206072176336297032333)
                ·
                  refine ⟨3194702277066126111387125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8519206072176336297032333 3194702277066126111387125)
                  ·
                    refine ⟨299503338474949322942543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3194702277066126111387125 299503338474949322942543)
                    ·
                      rfl

theorem cell23_1749842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1749842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749842 prefixEnd_1749842 := by exact prefixLift 1749842
  have htrace : WordTrace (prefixWord ++ tailWord_1749842) baseStart_1749842 baseEnd_1749842 := by
    simpa [prefixWord, tailWord_1749842, baseEnd_1749842] using wordTrace_append hprefix tailTrace_1749842
  have hstable : (prefixWord ++ tailWord_1749842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749842).length < 2 ^ (prefixWord ++ tailWord_1749842).sum := by decide
  have hdescent : baseEnd_1749842 < baseStart_1749842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749849 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 2, 3, 2]
def baseStart_1749849 : Nat := 118140960795 + 1749849 * 2 ^ 59
def prefixEnd_1749849 : Nat := 4983230072969 + 3 ^ 40 * 1749849 * 2
def baseEnd_1749849 : Nat := 898513609789429441440097

theorem tailTrace_1749849 : CollatzResearch.WordTrace tailWord_1749849 prefixEnd_1749849 898513609789429441440097 := by
  unfold tailWord_1749849
  simp only [CollatzResearch.WordTrace]
  refine ⟨63822236237603398261612601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42548157491735598841075067 63822236237603398261612601)
  ·
    refine ⟨47866677178202548696209451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63822236237603398261612601 47866677178202548696209451)
    ·
      refine ⟨71800015767303823044314177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47866677178202548696209451 71800015767303823044314177)
      ·
        refine ⟨53850011825477867283235633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71800015767303823044314177 53850011825477867283235633)
        ·
          refine ⟨40387508869108400462426725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53850011825477867283235633 40387508869108400462426725)
          ·
            refine ⟨7572657912957825086705011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40387508869108400462426725 7572657912957825086705011)
            ·
              refine ⟨11358986869436737630057517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572657912957825086705011 11358986869436737630057517)
              ·
                refine ⟨4259620076038776611271569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11358986869436737630057517 4259620076038776611271569)
                ·
                  refine ⟨3194715057029082458453677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259620076038776611271569 3194715057029082458453677)
                  ·
                    refine ⟨1198018146385905921920129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194715057029082458453677 1198018146385905921920129)
                    ·
                      refine ⟨898513609789429441440097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198018146385905921920129 898513609789429441440097)
                      ·
                        rfl

theorem cell23_1749849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_1749849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749849 prefixEnd_1749849 := by exact prefixLift 1749849
  have htrace : WordTrace (prefixWord ++ tailWord_1749849) baseStart_1749849 baseEnd_1749849 := by
    simpa [prefixWord, tailWord_1749849, baseEnd_1749849] using wordTrace_append hprefix tailTrace_1749849
  have hstable : (prefixWord ++ tailWord_1749849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749849).length < 2 ^ (prefixWord ++ tailWord_1749849).sum := by decide
  have hdescent : baseEnd_1749849 < baseStart_1749849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749856 : List Nat := [2, 1, 1, 3, 3, 1, 2, 5, 1, 1, 3]
def baseStart_1749856 : Nat := 118140960795 + 1749856 * 2 ^ 59
def prefixEnd_1749856 : Nat := 4983230072969 + 3 ^ 40 * 1749856 * 2
def baseEnd_1749856 : Nat := 898517204154010914052565

theorem tailTrace_1749856 : CollatzResearch.WordTrace tailWord_1749856 prefixEnd_1749856 898517204154010914052565 := by
  unfold tailWord_1749856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31911245774289019228558711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42548327699052025638078281 31911245774289019228558711)
  ·
    refine ⟨47866868661433528842838067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31911245774289019228558711 47866868661433528842838067)
    ·
      refine ⟨71800302992150293264257101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47866868661433528842838067 71800302992150293264257101)
      ·
        refine ⟨26925113622056359974096413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71800302992150293264257101 26925113622056359974096413)
        ·
          refine ⟨10096917608271134990286155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26925113622056359974096413 10096917608271134990286155)
          ·
            refine ⟨15145376412406702485429233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10096917608271134990286155 15145376412406702485429233)
            ·
              refine ⟨11359032309305026864071925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15145376412406702485429233 11359032309305026864071925)
              ·
                refine ⟨1064909278997346268506743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11359032309305026864071925 1064909278997346268506743)
                ·
                  refine ⟨1597363918496019402760115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064909278997346268506743 1597363918496019402760115)
                  ·
                    refine ⟨2396045877744029104140173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597363918496019402760115 2396045877744029104140173)
                    ·
                      refine ⟨898517204154010914052565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2396045877744029104140173 898517204154010914052565)
                      ·
                        rfl

theorem cell23_1749856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_1749856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749856 prefixEnd_1749856 := by exact prefixLift 1749856
  have htrace : WordTrace (prefixWord ++ tailWord_1749856) baseStart_1749856 baseEnd_1749856 := by
    simpa [prefixWord, tailWord_1749856, baseEnd_1749856] using wordTrace_append hprefix tailTrace_1749856
  have hstable : (prefixWord ++ tailWord_1749856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749856).length < 2 ^ (prefixWord ++ tailWord_1749856).sum := by decide
  have hdescent : baseEnd_1749856 < baseStart_1749856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749872 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 4, 4]
def baseStart_1749872 : Nat := 118140960795 + 1749872 * 2 ^ 59
def prefixEnd_1749872 : Nat := 4983230072969 + 3 ^ 40 * 1749872 * 2
def baseEnd_1749872 : Nat := 299508473281494283817497

theorem tailTrace_1749872 : CollatzResearch.WordTrace tailWord_1749872 prefixEnd_1749872 299508473281494283817497 := by
  unfold tailWord_1749872
  simp only [CollatzResearch.WordTrace]
  refine ⟨31911537558260036594849935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42548716744346715459799913 31911537558260036594849935)
  ·
    refine ⟨47867306337390054892274903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31911537558260036594849935 47867306337390054892274903)
    ·
      refine ⟨71800959506085082338412355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47867306337390054892274903 71800959506085082338412355)
      ·
        refine ⟨107701439259127623507618533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71800959506085082338412355 107701439259127623507618533)
        ·
          refine ⟨20194019861086429407678475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107701439259127623507618533 20194019861086429407678475)
          ·
            refine ⟨30291029791629644111517713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20194019861086429407678475 30291029791629644111517713)
            ·
              refine ⟨22718272343722233083638285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30291029791629644111517713 22718272343722233083638285)
              ·
                refine ⟨8519352128895837406364357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22718272343722233083638285 8519352128895837406364357)
                ·
                  refine ⟨1597378524167969513693317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8519352128895837406364357 1597378524167969513693317)
                  ·
                    refine ⟨299508473281494283817497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597378524167969513693317 299508473281494283817497)
                    ·
                      rfl

theorem cell23_1749872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_1749872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749872 prefixEnd_1749872 := by exact prefixLift 1749872
  have htrace : WordTrace (prefixWord ++ tailWord_1749872) baseStart_1749872 baseEnd_1749872 := by
    simpa [prefixWord, tailWord_1749872, baseEnd_1749872] using wordTrace_append hprefix tailTrace_1749872
  have hstable : (prefixWord ++ tailWord_1749872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749872).length < 2 ^ (prefixWord ++ tailWord_1749872).sum := by decide
  have hdescent : baseEnd_1749872 < baseStart_1749872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749873 : List Nat := [1, 2, 2, 2, 1, 4, 4, 2, 1, 1, 3]
def baseStart_1749873 : Nat := 118140960795 + 1749873 * 2 ^ 59
def prefixEnd_1749873 : Nat := 4983230072969 + 3 ^ 40 * 1749873 * 2
def baseEnd_1749873 : Nat := 898525933325137347539987

theorem tailTrace_1749873 : CollatzResearch.WordTrace tailWord_1749873 prefixEnd_1749873 898525933325137347539987 := by
  unfold tailWord_1749873
  simp only [CollatzResearch.WordTrace]
  refine ⟨63823111589516450360486273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42548741059677633573657515 63823111589516450360486273)
  ·
    refine ⟨47867333692137337770364705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63823111589516450360486273 47867333692137337770364705)
    ·
      refine ⟨35900500269103003327773529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47867333692137337770364705 35900500269103003327773529)
      ·
        refine ⟨26925375201827252495830147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35900500269103003327773529 26925375201827252495830147)
        ·
          refine ⟨40388062802740878743745221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26925375201827252495830147 40388062802740878743745221)
          ·
            refine ⟨7572761775513914764452229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40388062802740878743745221 7572761775513914764452229)
            ·
              refine ⟨1419892832908859018334793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7572761775513914764452229 1419892832908859018334793)
              ·
                refine ⟨1064919624681644263751095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419892832908859018334793 1064919624681644263751095)
                ·
                  refine ⟨1597379437022466395626643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064919624681644263751095 1597379437022466395626643)
                  ·
                    refine ⟨2396069155533699593439965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597379437022466395626643 2396069155533699593439965)
                    ·
                      refine ⟨898525933325137347539987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2396069155533699593439965 898525933325137347539987)
                      ·
                        rfl

theorem cell23_1749873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_1749873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749873 prefixEnd_1749873 := by exact prefixLift 1749873
  have htrace : WordTrace (prefixWord ++ tailWord_1749873) baseStart_1749873 baseEnd_1749873 := by
    simpa [prefixWord, tailWord_1749873, baseEnd_1749873] using wordTrace_append hprefix tailTrace_1749873
  have hstable : (prefixWord ++ tailWord_1749873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749873).length < 2 ^ (prefixWord ++ tailWord_1749873).sum := by decide
  have hdescent : baseEnd_1749873 < baseStart_1749873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749875 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6]
def baseStart_1749875 : Nat := 118140960795 + 1749875 * 2 ^ 59
def prefixEnd_1749875 : Nat := 4983230072969 + 3 ^ 40 * 1749875 * 2
def baseEnd_1749875 : Nat := 898526960286446339714977

theorem tailTrace_1749875 : CollatzResearch.WordTrace tailWord_1749875 prefixEnd_1749875 898526960286446339714977 := by
  unfold tailWord_1749875
  simp only [CollatzResearch.WordTrace]
  refine ⟨63823184535509204702059079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42548789690339469801372719 63823184535509204702059079)
  ·
    refine ⟨95734776803263807053088619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63823184535509204702059079 95734776803263807053088619)
    ·
      refine ⟨143602165204895710579632929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95734776803263807053088619 143602165204895710579632929)
      ·
        refine ⟨107701623903671782934724697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143602165204895710579632929 107701623903671782934724697)
        ·
          refine ⟨80776217927753837201043523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107701623903671782934724697 80776217927753837201043523)
          ·
            refine ⟨121164326891630755801565285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80776217927753837201043523 121164326891630755801565285)
            ·
              refine ⟨22718311292180766712793491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121164326891630755801565285 22718311292180766712793491)
              ·
                refine ⟨34077466938271150069190237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22718311292180766712793491 34077466938271150069190237)
                ·
                  refine ⟨12779050101851681275946339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34077466938271150069190237 12779050101851681275946339)
                  ·
                    refine ⟨19168575152777521913919509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12779050101851681275946339 19168575152777521913919509)
                    ·
                      refine ⟨898526960286446339714977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19168575152777521913919509 898526960286446339714977)
                      ·
                        rfl

theorem cell23_1749875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_1749875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749875 prefixEnd_1749875 := by exact prefixLift 1749875
  have htrace : WordTrace (prefixWord ++ tailWord_1749875) baseStart_1749875 baseEnd_1749875 := by
    simpa [prefixWord, tailWord_1749875, baseEnd_1749875] using wordTrace_append hprefix tailTrace_1749875
  have hstable : (prefixWord ++ tailWord_1749875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749875).length < 2 ^ (prefixWord ++ tailWord_1749875).sum := by decide
  have hdescent : baseEnd_1749875 < baseStart_1749875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749879 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 7, 2, 2]
def baseStart_1749879 : Nat := 118140960795 + 1749879 * 2 ^ 59
def prefixEnd_1749879 : Nat := 4983230072969 + 3 ^ 40 * 1749879 * 2
def baseEnd_1749879 : Nat := 898529014209064324064959

theorem tailTrace_1749879 : CollatzResearch.WordTrace tailWord_1749879 prefixEnd_1749879 898529014209064324064959 := by
  unfold tailWord_1749879
  simp only [CollatzResearch.WordTrace]
  refine ⟨63823330427494713385204691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42548886951663142256803127 63823330427494713385204691)
  ·
    refine ⟨95734995641242070077807037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63823330427494713385204691 95734995641242070077807037)
    ·
      refine ⟨35900623365465776279177639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95734995641242070077807037 35900623365465776279177639)
      ·
        refine ⟨53850935048198664418766459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35900623365465776279177639 53850935048198664418766459)
        ·
          refine ⟨80776402572297996628149689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53850935048198664418766459 80776402572297996628149689)
          ·
            refine ⟨60582301929223497471112267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80776402572297996628149689 60582301929223497471112267)
            ·
              refine ⟨90873452893835246206668401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60582301929223497471112267 90873452893835246206668401)
              ·
                refine ⟨68155089670376434655001301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90873452893835246206668401 68155089670376434655001301)
                ·
                  refine ⟨1597384914149447687226593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 68155089670376434655001301 1597384914149447687226593)
                  ·
                    refine ⟨1198038685612085765419945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1597384914149447687226593 1198038685612085765419945)
                    ·
                      refine ⟨898529014209064324064959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198038685612085765419945 898529014209064324064959)
                      ·
                        rfl

theorem cell23_1749879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_1749879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749879 prefixEnd_1749879 := by exact prefixLift 1749879
  have htrace : WordTrace (prefixWord ++ tailWord_1749879) baseStart_1749879 baseEnd_1749879 := by
    simpa [prefixWord, tailWord_1749879, baseEnd_1749879] using wordTrace_append hprefix tailTrace_1749879
  have hstable : (prefixWord ++ tailWord_1749879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749879).length < 2 ^ (prefixWord ++ tailWord_1749879).sum := by decide
  have hdescent : baseEnd_1749879 < baseStart_1749879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749890 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1749890 : Nat := 118140960795 + 1749890 * 2 ^ 59
def prefixEnd_1749890 : Nat := 4983230072969 + 3 ^ 40 * 1749890 * 2
def baseEnd_1749890 : Nat := 898534662496263781027409

theorem tailTrace_1749890 : CollatzResearch.WordTrace tailWord_1749890 prefixEnd_1749890 898534662496263781027409 := by
  unfold tailWord_1749890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955932907613715565963781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42549154420303241509236749 15955932907613715565963781)
  ·
    refine ⟨2991737420177571668618209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15955932907613715565963781 2991737420177571668618209)
    ·
      refine ⟨2243803065133178751463657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2991737420177571668618209 2243803065133178751463657)
      ·
        refine ⟨1682852298849884063597743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2243803065133178751463657 1682852298849884063597743)
        ·
          refine ⟨2524278448274826095396615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682852298849884063597743 2524278448274826095396615)
          ·
            refine ⟨3786417672412239143094923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524278448274826095396615 3786417672412239143094923)
            ·
              refine ⟨5679626508618358714642385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786417672412239143094923 5679626508618358714642385)
              ·
                refine ⟨4259719881463769035981789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5679626508618358714642385 4259719881463769035981789)
                ·
                  refine ⟨1597394955548913388493171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4259719881463769035981789 1597394955548913388493171)
                  ·
                    refine ⟨2396092433323370082739757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597394955548913388493171 2396092433323370082739757)
                    ·
                      refine ⟨898534662496263781027409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2396092433323370082739757 898534662496263781027409)
                      ·
                        rfl

theorem cell23_1749890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1749890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749890 prefixEnd_1749890 := by exact prefixLift 1749890
  have htrace : WordTrace (prefixWord ++ tailWord_1749890) baseStart_1749890 baseEnd_1749890 := by
    simpa [prefixWord, tailWord_1749890, baseEnd_1749890] using wordTrace_append hprefix tailTrace_1749890
  have hstable : (prefixWord ++ tailWord_1749890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749890).length < 2 ^ (prefixWord ++ tailWord_1749890).sum := by decide
  have hdescent : baseEnd_1749890 < baseStart_1749890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749896 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1749896 : Nat := 118140960795 + 1749896 * 2 ^ 59
def prefixEnd_1749896 : Nat := 4983230072969 + 3 ^ 40 * 1749896 * 2
def baseEnd_1749896 : Nat := 898537743380190757552381

theorem tailTrace_1749896 : CollatzResearch.WordTrace tailWord_1749896 prefixEnd_1749896 898537743380190757552381 := by
  unfold tailWord_1749896
  simp only [CollatzResearch.WordTrace]
  refine ⟨31911975234216562644286771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42549300312288750192382361 31911975234216562644286771)
  ·
    refine ⟨47867962851324843966430157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31911975234216562644286771 47867962851324843966430157)
    ·
      refine ⟨17950486069246816487411309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47867962851324843966430157 17950486069246816487411309)
      ·
        refine ⟨6731432275967556182779241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17950486069246816487411309 6731432275967556182779241)
        ·
          refine ⟨5048574206975667137084431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6731432275967556182779241 5048574206975667137084431)
          ·
            refine ⟨7572861310463500705626647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048574206975667137084431 7572861310463500705626647)
            ·
              refine ⟨11359291965695251058439971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572861310463500705626647 11359291965695251058439971)
              ·
                refine ⟨17038937948542876587659957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11359291965695251058439971 17038937948542876587659957)
                ·
                  refine ⟨1597400432675894680093121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17038937948542876587659957 1597400432675894680093121)
                  ·
                    refine ⟨1198050324506921010069841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1597400432675894680093121 1198050324506921010069841)
                    ·
                      refine ⟨898537743380190757552381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198050324506921010069841 898537743380190757552381)
                      ·
                        rfl

theorem cell23_1749896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1749896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749896 prefixEnd_1749896 := by exact prefixLift 1749896
  have htrace : WordTrace (prefixWord ++ tailWord_1749896) baseStart_1749896 baseEnd_1749896 := by
    simpa [prefixWord, tailWord_1749896, baseEnd_1749896] using wordTrace_append hprefix tailTrace_1749896
  have hstable : (prefixWord ++ tailWord_1749896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749896).length < 2 ^ (prefixWord ++ tailWord_1749896).sum := by decide
  have hdescent : baseEnd_1749896 < baseStart_1749896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749910 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1749910 : Nat := 118140960795 + 1749910 * 2 ^ 59
def prefixEnd_1749910 : Nat := 4983230072969 + 3 ^ 40 * 1749910 * 2
def baseEnd_1749910 : Nat := 299514977369784567592439

theorem tailTrace_1749910 : CollatzResearch.WordTrace tailWord_1749910 prefixEnd_1749910 299514977369784567592439 := by
  unfold tailWord_1749910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989028818148900354973949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42549640726921603786388789 3989028818148900354973949)
  ·
    refine ⟨1495885806805837633115231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3989028818148900354973949 1495885806805837633115231)
    ·
      refine ⟨2243828710208756449672847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495885806805837633115231 2243828710208756449672847)
      ·
        refine ⟨3365743065313134674509271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243828710208756449672847 3365743065313134674509271)
        ·
          refine ⟨5048614597969702011763907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365743065313134674509271 5048614597969702011763907)
          ·
            refine ⟨7572921896954553017645861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048614597969702011763907 7572921896954553017645861)
            ·
              refine ⟨1419922855678978690808599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7572921896954553017645861 1419922855678978690808599)
              ·
                refine ⟨2129884283518468036212899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419922855678978690808599 2129884283518468036212899)
                ·
                  refine ⟨3194826425277702054319349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129884283518468036212899 3194826425277702054319349)
                  ·
                    refine ⟨299514977369784567592439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3194826425277702054319349 299514977369784567592439)
                    ·
                      rfl

theorem cell23_1749910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1749910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749910 prefixEnd_1749910 := by exact prefixLift 1749910
  have htrace : WordTrace (prefixWord ++ tailWord_1749910) baseStart_1749910 baseEnd_1749910 := by
    simpa [prefixWord, tailWord_1749910, baseEnd_1749910] using wordTrace_append hprefix tailTrace_1749910
  have hstable : (prefixWord ++ tailWord_1749910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749910).length < 2 ^ (prefixWord ++ tailWord_1749910).sum := by decide
  have hdescent : baseEnd_1749910 < baseStart_1749910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749929 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 3]
def baseStart_1749929 : Nat := 118140960795 + 1749929 * 2 ^ 59
def prefixEnd_1749929 : Nat := 4983230072969 + 3 ^ 40 * 1749929 * 2
def baseEnd_1749929 : Nat := 898554688241789128439729

theorem tailTrace_1749929 : CollatzResearch.WordTrace tailWord_1749929 prefixEnd_1749929 898554688241789128439729 := by
  unfold tailWord_1749929
  simp only [CollatzResearch.WordTrace]
  refine ⟨63825154077313571924524841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42550102718209047949683227 63825154077313571924524841)
  ·
    refine ⟨47868865557985178943393631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63825154077313571924524841 47868865557985178943393631)
    ·
      refine ⟨71803298336977768415090447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47868865557985178943393631 71803298336977768415090447)
      ·
        refine ⟨107704947505466652622635671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71803298336977768415090447 107704947505466652622635671)
        ·
          refine ⟨161557421258199978933953507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107704947505466652622635671 161557421258199978933953507)
          ·
            refine ⟨242336131887299968400930261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161557421258199978933953507 242336131887299968400930261)
            ·
              refine ⟨5679753091108593009396803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 242336131887299968400930261 5679753091108593009396803)
              ·
                refine ⟨8519629636662889514095205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679753091108593009396803 8519629636662889514095205)
                ·
                  refine ⟨1597430556874291783892851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8519629636662889514095205 1597430556874291783892851)
                  ·
                    refine ⟨2396145835311437675839277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597430556874291783892851 2396145835311437675839277)
                    ·
                      refine ⟨898554688241789128439729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2396145835311437675839277 898554688241789128439729)
                      ·
                        rfl

theorem cell23_1749929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 3].length) (baseStart_1749929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749929 prefixEnd_1749929 := by exact prefixLift 1749929
  have htrace : WordTrace (prefixWord ++ tailWord_1749929) baseStart_1749929 baseEnd_1749929 := by
    simpa [prefixWord, tailWord_1749929, baseEnd_1749929] using wordTrace_append hprefix tailTrace_1749929
  have hstable : (prefixWord ++ tailWord_1749929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749929).length < 2 ^ (prefixWord ++ tailWord_1749929).sum := by decide
  have hdescent : baseEnd_1749929 < baseStart_1749929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749939 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 3, 3, 2]
def baseStart_1749939 : Nat := 118140960795 + 1749939 * 2 ^ 59
def prefixEnd_1749939 : Nat := 4983230072969 + 3 ^ 40 * 1749939 * 2
def baseEnd_1749939 : Nat := 898559823048334089314683

theorem tailTrace_1749939 : CollatzResearch.WordTrace tailWord_1749939 prefixEnd_1749939 898559823048334089314683 := by
  unfold tailWord_1749939
  simp only [CollatzResearch.WordTrace]
  refine ⟨63825518807277343632388871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42550345871518229088259247 63825518807277343632388871)
  ·
    refine ⟨95738278210916015448583307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63825518807277343632388871 95738278210916015448583307)
    ·
      refine ⟨143607417316374023172874961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95738278210916015448583307 143607417316374023172874961)
      ·
        refine ⟨107705562987280517379656221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143607417316374023172874961 107705562987280517379656221)
        ·
          refine ⟨40389586120230194017371083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107705562987280517379656221 40389586120230194017371083)
          ·
            refine ⟨60584379180345291026056625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40389586120230194017371083 60584379180345291026056625)
            ·
              refine ⟨45438284385258968269542469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60584379180345291026056625 45438284385258968269542469)
              ·
                refine ⟨8519678322236056550539213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45438284385258968269542469 8519678322236056550539213)
                ·
                  refine ⟨3194879370838521206452205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8519678322236056550539213 3194879370838521206452205)
                  ·
                    refine ⟨1198079764064445452419577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194879370838521206452205 1198079764064445452419577)
                    ·
                      refine ⟨898559823048334089314683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198079764064445452419577 898559823048334089314683)
                      ·
                        rfl

theorem cell23_1749939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3, 2].length) (baseStart_1749939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749939 prefixEnd_1749939 := by exact prefixLift 1749939
  have htrace : WordTrace (prefixWord ++ tailWord_1749939) baseStart_1749939 baseEnd_1749939 := by
    simpa [prefixWord, tailWord_1749939, baseEnd_1749939] using wordTrace_append hprefix tailTrace_1749939
  have hstable : (prefixWord ++ tailWord_1749939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749939).length < 2 ^ (prefixWord ++ tailWord_1749939).sum := by decide
  have hdescent : baseEnd_1749939 < baseStart_1749939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749940 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1749940 : Nat := 118140960795 + 1749940 * 2 ^ 59
def prefixEnd_1749940 : Nat := 4983230072969 + 3 ^ 40 * 1749940 * 2
def baseEnd_1749940 : Nat := 299520112176329528467393

theorem tailTrace_1749940 : CollatzResearch.WordTrace tailWord_1749940 prefixEnd_1749940 299520112176329528467393 := by
  unfold tailWord_1749940
  simp only [CollatzResearch.WordTrace]
  refine ⟨31912777640136860401587637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42550370186849147202116849 31912777640136860401587637)
  ·
    refine ⟨2991822903762830662648841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31912777640136860401587637 2991822903762830662648841)
    ·
      refine ⟨2243867177822122996986631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2991822903762830662648841 2243867177822122996986631)
      ·
        refine ⟨3365800766733184495479947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243867177822122996986631 3365800766733184495479947)
        ·
          refine ⟨5048701150099776743219921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365800766733184495479947 5048701150099776743219921)
          ·
            refine ⟨3786525862574832557414941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5048701150099776743219921 3786525862574832557414941)
            ·
              refine ⟨1419947198465562209030603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3786525862574832557414941 1419947198465562209030603)
              ·
                refine ⟨2129920797698343313545905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419947198465562209030603 2129920797698343313545905)
                ·
                  refine ⟨1597440598273757485159429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2129920797698343313545905 1597440598273757485159429)
                  ·
                    refine ⟨299520112176329528467393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597440598273757485159429 299520112176329528467393)
                    ·
                      rfl

theorem cell23_1749940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1749940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749940 prefixEnd_1749940 := by exact prefixLift 1749940
  have htrace : WordTrace (prefixWord ++ tailWord_1749940) baseStart_1749940 baseEnd_1749940 := by
    simpa [prefixWord, tailWord_1749940, baseEnd_1749940] using wordTrace_append hprefix tailTrace_1749940
  have hstable : (prefixWord ++ tailWord_1749940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749940).length < 2 ^ (prefixWord ++ tailWord_1749940).sum := by decide
  have hdescent : baseEnd_1749940 < baseStart_1749940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749958 : List Nat := [6, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1749958 : Nat := 118140960795 + 1749958 * 2 ^ 59
def prefixEnd_1749958 : Nat := 4983230072969 + 3 ^ 40 * 1749958 * 2
def baseEnd_1749958 : Nat := 898569579180769514977097

theorem tailTrace_1749958 : CollatzResearch.WordTrace tailWord_1749958 prefixEnd_1749958 898569579180769514977097 := by
  unfold tailWord_1749958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994569118569015933666579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42550807862805673251553685 1994569118569015933666579)
  ·
    refine ⟨2991853677853523900499869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1994569118569015933666579 2991853677853523900499869)
    ·
      refine ⟨1121945129195071462687451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2991853677853523900499869 1121945129195071462687451)
      ·
        refine ⟨1682917693792607194031177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121945129195071462687451 1682917693792607194031177)
        ·
          refine ⟨1262188270344455395523383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682917693792607194031177 1262188270344455395523383)
          ·
            refine ⟨1893282405516683093285075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262188270344455395523383 1893282405516683093285075)
            ·
              refine ⟨2839923608275024639927613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893282405516683093285075 2839923608275024639927613)
              ·
                refine ⟨1064971353103134239972855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2839923608275024639927613 1064971353103134239972855)
                ·
                  refine ⟨1597457029654701359959283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064971353103134239972855 1597457029654701359959283)
                  ·
                    refine ⟨2396185544482052039938925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597457029654701359959283 2396185544482052039938925)
                    ·
                      refine ⟨898569579180769514977097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2396185544482052039938925 898569579180769514977097)
                      ·
                        rfl

theorem cell23_1749958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1749958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749958 prefixEnd_1749958 := by exact prefixLift 1749958
  have htrace : WordTrace (prefixWord ++ tailWord_1749958) baseStart_1749958 baseEnd_1749958 := by
    simpa [prefixWord, tailWord_1749958, baseEnd_1749958] using wordTrace_append hprefix tailTrace_1749958
  have hstable : (prefixWord ++ tailWord_1749958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749958).length < 2 ^ (prefixWord ++ tailWord_1749958).sum := by decide
  have hdescent : baseEnd_1749958 < baseStart_1749958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
