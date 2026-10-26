import V185TrunkScan23Chunk0808

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4785566 : List Nat := [4, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_4785566 : Nat := 118140960795 + 4785566 * 2 ^ 59
def prefixEnd_4785566 : Nat := 4983230072969 + 3 ^ 40 * 4785566 * 2
def baseEnd_4785566 : Nat := 273032840201592076079621

theorem tailTrace_4785566 : CollatzResearch.WordTrace tailWord_4785566 prefixEnd_4785566 273032840201592076079621 := by
  unfold tailWord_4785566
  simp only [CollatzResearch.WordTrace]
  refine ⟨21817991422589895806071069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116362620920479444299045701 21817991422589895806071069)
  ·
    refine ⟨8181746783471210927276651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21817991422589895806071069 8181746783471210927276651)
    ·
      refine ⟨12272620175206816390914977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8181746783471210927276651 12272620175206816390914977)
      ·
        refine ⟨9204465131405112293186233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12272620175206816390914977 9204465131405112293186233)
        ·
          refine ⟨6903348848553834219889675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9204465131405112293186233 6903348848553834219889675)
          ·
            refine ⟨10355023272830751329834513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6903348848553834219889675 10355023272830751329834513)
            ·
              refine ⟨7766267454623063497375885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10355023272830751329834513 7766267454623063497375885)
              ·
                refine ⟨2912350295483648811515957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7766267454623063497375885 2912350295483648811515957)
                ·
                  refine ⟨273032840201592076079621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2912350295483648811515957 273032840201592076079621)
                  ·
                    rfl

theorem cell23_4785566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_4785566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785566 prefixEnd_4785566 := by exact prefixLift 4785566
  have htrace : WordTrace (prefixWord ++ tailWord_4785566) baseStart_4785566 baseEnd_4785566 := by
    simpa [prefixWord, tailWord_4785566, baseEnd_4785566] using wordTrace_append hprefix tailTrace_4785566
  have hstable : (prefixWord ++ tailWord_4785566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785566).length < 2 ^ (prefixWord ++ tailWord_4785566).sum := by decide
  have hdescent : baseEnd_4785566 < baseStart_4785566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785622 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_4785622 : Nat := 118140960795 + 4785622 * 2 ^ 59
def prefixEnd_4785622 : Nat := 4983230072969 + 3 ^ 40 * 4785622 * 2
def baseEnd_4785622 : Nat := 273036035192331162846259

theorem tailTrace_4785622 : CollatzResearch.WordTrace tailWord_4785622 prefixEnd_4785622 273036035192331162846259 := by
  unfold tailWord_4785622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909123366782268000787945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116363982579010858675071413 10909123366782268000787945)
  ·
    refine ⟨8181842525086701000590959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10909123366782268000787945 8181842525086701000590959)
    ·
      refine ⟨12272763787630051500886439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8181842525086701000590959 12272763787630051500886439)
      ·
        refine ⟨18409145681445077251329659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12272763787630051500886439 18409145681445077251329659)
        ·
          refine ⟨27613718522167615876994489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18409145681445077251329659 27613718522167615876994489)
          ·
            refine ⟨20710288891625711907745867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27613718522167615876994489 20710288891625711907745867)
            ·
              refine ⟨31065433337438567861618801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20710288891625711907745867 31065433337438567861618801)
              ·
                refine ⟨23299075003078925896214101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31065433337438567861618801 23299075003078925896214101)
                ·
                  refine ⟨273036035192331162846259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23299075003078925896214101 273036035192331162846259)
                  ·
                    rfl

theorem cell23_4785622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_4785622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785622 prefixEnd_4785622 := by exact prefixLift 4785622
  have htrace : WordTrace (prefixWord ++ tailWord_4785622) baseStart_4785622 baseEnd_4785622 := by
    simpa [prefixWord, tailWord_4785622, baseEnd_4785622] using wordTrace_append hprefix tailTrace_4785622
  have hstable : (prefixWord ++ tailWord_4785622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785622).length < 2 ^ (prefixWord ++ tailWord_4785622).sum := by decide
  have hdescent : baseEnd_4785622 < baseStart_4785622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785626 : List Nat := [3, 1, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_4785626 : Nat := 118140960795 + 4785626 * 2 ^ 59
def prefixEnd_4785626 : Nat := 4983230072969 + 3 ^ 40 * 4785626 * 2
def baseEnd_4785626 : Nat := 819108790217866149988771

theorem tailTrace_4785626 : CollatzResearch.WordTrace tailWord_4785626 prefixEnd_4785626 819108790217866149988771 := by
  unfold tailWord_4785626
  simp only [CollatzResearch.WordTrace]
  refine ⟨43636529940125449173938183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116364079840334531130501821 43636529940125449173938183)
  ·
    refine ⟨65454794910188173760907275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43636529940125449173938183 65454794910188173760907275)
    ·
      refine ⟨98182192365282260641360913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65454794910188173760907275 98182192365282260641360913)
      ·
        refine ⟨73636644273961695481020685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98182192365282260641360913 73636644273961695481020685)
        ·
          refine ⟨27613741602735635805382757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73636644273961695481020685 27613741602735635805382757)
          ·
            refine ⟨5177576550512931713509267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27613741602735635805382757 5177576550512931713509267)
            ·
              refine ⟨7766364825769397570263901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5177576550512931713509267 7766364825769397570263901)
              ·
                refine ⟨2912386809663524088848963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7766364825769397570263901 2912386809663524088848963)
                ·
                  refine ⟨4368580214495286133273445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912386809663524088848963 4368580214495286133273445)
                  ·
                    refine ⟨819108790217866149988771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4368580214495286133273445 819108790217866149988771)
                    ·
                      rfl

theorem cell23_4785626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_4785626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785626 prefixEnd_4785626 := by exact prefixLift 4785626
  have htrace : WordTrace (prefixWord ++ tailWord_4785626) baseStart_4785626 baseEnd_4785626 := by
    simpa [prefixWord, tailWord_4785626, baseEnd_4785626] using wordTrace_append hprefix tailTrace_4785626
  have hstable : (prefixWord ++ tailWord_4785626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785626).length < 2 ^ (prefixWord ++ tailWord_4785626).sum := by decide
  have hdescent : baseEnd_4785626 < baseStart_4785626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785649 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_4785649 : Nat := 118140960795 + 4785649 * 2 ^ 59
def prefixEnd_4785649 : Nat := 4983230072969 + 3 ^ 40 * 4785649 * 2
def baseEnd_4785649 : Nat := 2457338180708651859978707

theorem tailTrace_4785649 : CollatzResearch.WordTrace tailWord_4785649 prefixEnd_4785649 2457338180708651859978707 := by
  unfold tailWord_4785649
  simp only [CollatzResearch.WordTrace]
  refine ⟨174546958639418471623840001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116364639092945647749226667 174546958639418471623840001)
  ·
    refine ⟨130910218979563853717880001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174546958639418471623840001 130910218979563853717880001)
    ·
      refine ⟨98182664234672890288410001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130910218979563853717880001 98182664234672890288410001)
      ·
        refine ⟨73636998176004667716307501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98182664234672890288410001 73636998176004667716307501)
        ·
          refine ⟨27613874316001750393615313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73636998176004667716307501 27613874316001750393615313)
          ·
            refine ⟨20710405737001312795211485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27613874316001750393615313 20710405737001312795211485)
            ·
              refine ⟨7766402151375492298204307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20710405737001312795211485 7766402151375492298204307)
              ·
                refine ⟨11649603227063238447306461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7766402151375492298204307 11649603227063238447306461)
                ·
                  refine ⟨4368601210148714417739923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11649603227063238447306461 4368601210148714417739923)
                  ·
                    refine ⟨6552901815223071626609885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4368601210148714417739923 6552901815223071626609885)
                    ·
                      refine ⟨2457338180708651859978707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6552901815223071626609885 2457338180708651859978707)
                      ·
                        rfl

theorem cell23_4785649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_4785649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785649 prefixEnd_4785649 := by exact prefixLift 4785649
  have htrace : WordTrace (prefixWord ++ tailWord_4785649) baseStart_4785649 baseEnd_4785649 := by
    simpa [prefixWord, tailWord_4785649, baseEnd_4785649] using wordTrace_append hprefix tailTrace_4785649
  have hstable : (prefixWord ++ tailWord_4785649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785649).length < 2 ^ (prefixWord ++ tailWord_4785649).sum := by decide
  have hdescent : baseEnd_4785649 < baseStart_4785649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785670 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4785670 : Nat := 118140960795 + 4785670 * 2 ^ 59
def prefixEnd_4785670 : Nat := 4983230072969 + 3 ^ 40 * 4785670 * 2
def baseEnd_4785670 : Nat := 2457348963802396277816111

theorem tailTrace_4785670 : CollatzResearch.WordTrace tailWord_4785670 prefixEnd_4785670 2457348963802396277816111 := by
  unfold tailWord_4785670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454616392885699756573577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116365149714894928140236309 5454616392885699756573577)
  ·
    refine ⟨4090962294664274817430183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5454616392885699756573577 4090962294664274817430183)
    ·
      refine ⟨6136443441996412226145275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4090962294664274817430183 6136443441996412226145275)
      ·
        refine ⟨9204665162994618339217913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6136443441996412226145275 9204665162994618339217913)
        ·
          refine ⟨6903498872245963754413435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9204665162994618339217913 6903498872245963754413435)
          ·
            refine ⟨10355248308368945631620153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6903498872245963754413435 10355248308368945631620153)
            ·
              refine ⟨7766436231276709223715115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10355248308368945631620153 7766436231276709223715115)
              ·
                refine ⟨11649654346915063835572673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7766436231276709223715115 11649654346915063835572673)
                ·
                  refine ⟨8737240760186297876679505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11649654346915063835572673 8737240760186297876679505)
                  ·
                    refine ⟨6552930570139723407509629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8737240760186297876679505 6552930570139723407509629)
                    ·
                      refine ⟨2457348963802396277816111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6552930570139723407509629 2457348963802396277816111)
                      ·
                        rfl

theorem cell23_4785670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4785670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785670 prefixEnd_4785670 := by exact prefixLift 4785670
  have htrace : WordTrace (prefixWord ++ tailWord_4785670) baseStart_4785670 baseEnd_4785670 := by
    simpa [prefixWord, tailWord_4785670, baseEnd_4785670] using wordTrace_append hprefix tailTrace_4785670
  have hstable : (prefixWord ++ tailWord_4785670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785670).length < 2 ^ (prefixWord ++ tailWord_4785670).sum := by decide
  have hdescent : baseEnd_4785670 < baseStart_4785670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785672 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_4785672 : Nat := 118140960795 + 4785672 * 2 ^ 59
def prefixEnd_4785672 : Nat := 4983230072969 + 3 ^ 40 * 4785672 * 2
def baseEnd_4785672 : Nat := 2457349990763705269991101

theorem tailTrace_4785672 : CollatzResearch.WordTrace tailWord_4785672 prefixEnd_4785672 2457349990763705269991101 := by
  unfold tailWord_4785672
  simp only [CollatzResearch.WordTrace]
  refine ⟨87273898759167573275963635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116365198345556764367951513 87273898759167573275963635)
  ·
    refine ⟨130910848138751359913945453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87273898759167573275963635 130910848138751359913945453)
    ·
      refine ⟨49091568052031759967729545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130910848138751359913945453 49091568052031759967729545)
      ·
        refine ⟨36818676039023819975797159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49091568052031759967729545 36818676039023819975797159)
        ·
          refine ⟨55228014058535729963695739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36818676039023819975797159 55228014058535729963695739)
          ·
            refine ⟨82842021087803594945543609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55228014058535729963695739 82842021087803594945543609)
            ·
              refine ⟨62131515815852696209157707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82842021087803594945543609 62131515815852696209157707)
              ·
                refine ⟨93197273723779044313736561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62131515815852696209157707 93197273723779044313736561)
                ·
                  refine ⟨69897955292834283235302421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93197273723779044313736561 69897955292834283235302421)
                  ·
                    refine ⟨3276466654351607026654801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69897955292834283235302421 3276466654351607026654801)
                    ·
                      refine ⟨2457349990763705269991101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276466654351607026654801 2457349990763705269991101)
                      ·
                        rfl

theorem cell23_4785672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_4785672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785672 prefixEnd_4785672 := by exact prefixLift 4785672
  have htrace : WordTrace (prefixWord ++ tailWord_4785672) baseStart_4785672 baseEnd_4785672 := by
    simpa [prefixWord, tailWord_4785672, baseEnd_4785672] using wordTrace_append hprefix tailTrace_4785672
  have hstable : (prefixWord ++ tailWord_4785672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785672).length < 2 ^ (prefixWord ++ tailWord_4785672).sum := by decide
  have hdescent : baseEnd_4785672 < baseStart_4785672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785676 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 2, 3, 2]
def baseStart_4785676 : Nat := 118140960795 + 4785676 * 2 ^ 59
def prefixEnd_4785676 : Nat := 4983230072969 + 3 ^ 40 * 4785676 * 2
def baseEnd_4785676 : Nat := 2457352044686323254341083

theorem tailTrace_4785676 : CollatzResearch.WordTrace tailWord_4785676 prefixEnd_4785676 2457352044686323254341083 := by
  unfold tailWord_4785676
  simp only [CollatzResearch.WordTrace]
  refine ⟨87273971705160327617536441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116365295606880436823381921 87273971705160327617536441)
  ·
    refine ⟨65455478778870245713152331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87273971705160327617536441 65455478778870245713152331)
    ·
      refine ⟨98183218168305368569728497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65455478778870245713152331 98183218168305368569728497)
      ·
        refine ⟨73637413626229026427296373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98183218168305368569728497 73637413626229026427296373)
        ·
          refine ⟨6903507527458971227559035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73637413626229026427296373 6903507527458971227559035)
          ·
            refine ⟨10355261291188456841338553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6903507527458971227559035 10355261291188456841338553)
            ·
              refine ⟨7766445968391342631003915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10355261291188456841338553 7766445968391342631003915)
              ·
                refine ⟨11649668952587013946505873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7766445968391342631003915 11649668952587013946505873)
                ·
                  refine ⟨8737251714440260459879405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11649668952587013946505873 8737251714440260459879405)
                  ·
                    refine ⟨3276469392915097672454777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8737251714440260459879405 3276469392915097672454777)
                    ·
                      refine ⟨2457352044686323254341083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276469392915097672454777 2457352044686323254341083)
                      ·
                        rfl

theorem cell23_4785676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_4785676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785676 prefixEnd_4785676 := by exact prefixLift 4785676
  have htrace : WordTrace (prefixWord ++ tailWord_4785676) baseStart_4785676 baseEnd_4785676 := by
    simpa [prefixWord, tailWord_4785676, baseEnd_4785676] using wordTrace_append hprefix tailTrace_4785676
  have hstable : (prefixWord ++ tailWord_4785676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785676).length < 2 ^ (prefixWord ++ tailWord_4785676).sum := by decide
  have hdescent : baseEnd_4785676 < baseStart_4785676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785694 : List Nat := [4, 3, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4785694 : Nat := 118140960795 + 4785694 * 2 ^ 59
def prefixEnd_4785694 : Nat := 4983230072969 + 3 ^ 40 * 4785694 * 2
def baseEnd_4785694 : Nat := 819120429112701394638667

theorem tailTrace_4785694 : CollatzResearch.WordTrace tailWord_4785694 prefixEnd_4785694 819120429112701394638667 := by
  unfold tailWord_4785694
  simp only [CollatzResearch.WordTrace]
  refine ⟨21818574990531930538653517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116365733282836962872818757 21818574990531930538653517)
  ·
    refine ⟨8181965621449473951995069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21818574990531930538653517 8181965621449473951995069)
    ·
      refine ⟨3068237108043552731998151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8181965621449473951995069 3068237108043552731998151)
      ·
        refine ⟨4602355662065329097997227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068237108043552731998151 4602355662065329097997227)
        ·
          refine ⟨6903533493097993646995841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602355662065329097997227 6903533493097993646995841)
          ·
            refine ⟨5177650119823495235246881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6903533493097993646995841 5177650119823495235246881)
            ·
              refine ⟨3883237589867621426435161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177650119823495235246881 3883237589867621426435161)
              ·
                refine ⟨2912428192400716069826371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3883237589867621426435161 2912428192400716069826371)
                ·
                  refine ⟨4368642288601074104739557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912428192400716069826371 4368642288601074104739557)
                  ·
                    refine ⟨819120429112701394638667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4368642288601074104739557 819120429112701394638667)
                    ·
                      rfl

theorem cell23_4785694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4785694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785694 prefixEnd_4785694 := by exact prefixLift 4785694
  have htrace : WordTrace (prefixWord ++ tailWord_4785694) baseStart_4785694 baseEnd_4785694 := by
    simpa [prefixWord, tailWord_4785694, baseEnd_4785694] using wordTrace_append hprefix tailTrace_4785694
  have hstable : (prefixWord ++ tailWord_4785694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785694).length < 2 ^ (prefixWord ++ tailWord_4785694).sum := by decide
  have hdescent : baseEnd_4785694 < baseStart_4785694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785706 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4785706 : Nat := 118140960795 + 4785706 * 2 ^ 59
def prefixEnd_4785706 : Nat := 4983230072969 + 3 ^ 40 * 4785706 * 2
def baseEnd_4785706 : Nat := 2457367449105958136965945

theorem tailTrace_4785706 : CollatzResearch.WordTrace tailWord_4785706 prefixEnd_4785706 2457367449105958136965945 := by
  unfold tailWord_4785706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43637259400052992589666243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116366025066807980239109981 43637259400052992589666243)
  ·
    refine ⟨65455889100079488884499365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43637259400052992589666243 65455889100079488884499365)
    ·
      refine ⟨12272979206264904165843631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65455889100079488884499365 12272979206264904165843631)
      ·
        refine ⟨18409468809397356248765447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12272979206264904165843631 18409468809397356248765447)
        ·
          refine ⟨27614203214096034373148171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18409468809397356248765447 27614203214096034373148171)
          ·
            refine ⟨41421304821144051559722257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27614203214096034373148171 41421304821144051559722257)
            ·
              refine ⟨31065978615858038669791693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41421304821144051559722257 31065978615858038669791693)
              ·
                refine ⟨11649741980946764501171885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31065978615858038669791693 11649741980946764501171885)
                ·
                  refine ⟨4368653242855036687939457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11649741980946764501171885 4368653242855036687939457)
                  ·
                    refine ⟨3276489932141277515954593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4368653242855036687939457 3276489932141277515954593)
                    ·
                      refine ⟨2457367449105958136965945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276489932141277515954593 2457367449105958136965945)
                      ·
                        rfl

theorem cell23_4785706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4785706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785706 prefixEnd_4785706 := by exact prefixLift 4785706
  have htrace : WordTrace (prefixWord ++ tailWord_4785706) baseStart_4785706 baseEnd_4785706 := by
    simpa [prefixWord, tailWord_4785706, baseEnd_4785706] using wordTrace_append hprefix tailTrace_4785706
  have hstable : (prefixWord ++ tailWord_4785706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785706).length < 2 ^ (prefixWord ++ tailWord_4785706).sum := by decide
  have hdescent : baseEnd_4785706 < baseStart_4785706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785756 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_4785756 : Nat := 118140960795 + 4785756 * 2 ^ 59
def prefixEnd_4785756 : Nat := 4983230072969 + 3 ^ 40 * 4785756 * 2
def baseEnd_4785756 : Nat := 2457393123138682941340715

theorem tailTrace_4785756 : CollatzResearch.WordTrace tailWord_4785756 prefixEnd_4785756 2457393123138682941340715 := by
  unfold tailWord_4785756
  simp only [CollatzResearch.WordTrace]
  refine ⟨87275430625015414448992561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116367240833353885931990081 87275430625015414448992561)
  ·
    refine ⟨65456572968761560836744421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87275430625015414448992561 65456572968761560836744421)
    ·
      refine ⟨12273107431642792656889579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65456572968761560836744421 12273107431642792656889579)
      ·
        refine ⟨18409661147464188985334369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12273107431642792656889579 18409661147464188985334369)
        ·
          refine ⟨13807245860598141739000777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18409661147464188985334369 13807245860598141739000777)
          ·
            refine ⟨10355434395448606304250583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13807245860598141739000777 10355434395448606304250583)
            ·
              refine ⟨15533151593172909456375875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10355434395448606304250583 15533151593172909456375875)
              ·
                refine ⟨23299727389759364184563813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15533151593172909456375875 23299727389759364184563813)
                ·
                  refine ⟨4368698885579880784605715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23299727389759364184563813 4368698885579880784605715)
                  ·
                    refine ⟨6553048328369821176908573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4368698885579880784605715 6553048328369821176908573)
                    ·
                      refine ⟨2457393123138682941340715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553048328369821176908573 2457393123138682941340715)
                      ·
                        rfl

theorem cell23_4785756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_4785756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785756 prefixEnd_4785756 := by exact prefixLift 4785756
  have htrace : WordTrace (prefixWord ++ tailWord_4785756) baseStart_4785756 baseEnd_4785756 := by
    simpa [prefixWord, tailWord_4785756, baseEnd_4785756] using wordTrace_append hprefix tailTrace_4785756
  have hstable : (prefixWord ++ tailWord_4785756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785756).length < 2 ^ (prefixWord ++ tailWord_4785756).sum := by decide
  have hdescent : baseEnd_4785756 < baseStart_4785756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785773 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_4785773 : Nat := 118140960795 + 4785773 * 2 ^ 59
def prefixEnd_4785773 : Nat := 4983230072969 + 3 ^ 40 * 4785773 * 2
def baseEnd_4785773 : Nat := 2457401852309809374828137

theorem tailTrace_4785773 : CollatzResearch.WordTrace tailWord_4785773 prefixEnd_4785773 2457401852309809374828137 := by
  unfold tailWord_4785773
  simp only [CollatzResearch.WordTrace]
  refine ⟨174551481290969240801353973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116367654193979493867569315 174551481290969240801353973)
  ·
    refine ⟨16364201371028366325126935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174551481290969240801353973 16364201371028366325126935)
    ·
      refine ⟨24546302056542549487690403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16364201371028366325126935 24546302056542549487690403)
      ·
        refine ⟨36819453084813824231535605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24546302056542549487690403 36819453084813824231535605)
        ·
          refine ⟨3451823726701296021706463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36819453084813824231535605 3451823726701296021706463)
          ·
            refine ⟨5177735590051944032559695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451823726701296021706463 5177735590051944032559695)
            ·
              refine ⟨7766603385077916048839543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5177735590051944032559695 7766603385077916048839543)
              ·
                refine ⟨11649905077616874073259315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7766603385077916048839543 11649905077616874073259315)
                ·
                  refine ⟨17474857616425311109888973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11649905077616874073259315 17474857616425311109888973)
                  ·
                    refine ⟨6553071606159491666208365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17474857616425311109888973 6553071606159491666208365)
                    ·
                      refine ⟨2457401852309809374828137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553071606159491666208365 2457401852309809374828137)
                      ·
                        rfl

theorem cell23_4785773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_4785773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785773 prefixEnd_4785773 := by exact prefixLift 4785773
  have htrace : WordTrace (prefixWord ++ tailWord_4785773) baseStart_4785773 baseEnd_4785773 := by
    simpa [prefixWord, tailWord_4785773, baseEnd_4785773] using wordTrace_append hprefix tailTrace_4785773
  have hstable : (prefixWord ++ tailWord_4785773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785773).length < 2 ^ (prefixWord ++ tailWord_4785773).sum := by decide
  have hdescent : baseEnd_4785773 < baseStart_4785773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785879 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 3, 4]
def baseStart_4785879 : Nat := 118140960795 + 4785879 * 2 ^ 59
def prefixEnd_4785879 : Nat := 4983230072969 + 3 ^ 40 * 4785879 * 2
def baseEnd_4785879 : Nat := 819152093753061986700883

theorem tailTrace_4785879 : CollatzResearch.WordTrace tailWord_4785879 prefixEnd_4785879 819152093753061986700883 := by
  unfold tailWord_4785879
  simp only [CollatzResearch.WordTrace]
  refine ⟨174555347428585220904712691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116370231619056813936475127 174555347428585220904712691)
  ·
    refine ⟨261833021142877831357069037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174555347428585220904712691 261833021142877831357069037)
    ·
      refine ⟨98187382928579186758900889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261833021142877831357069037 98187382928579186758900889)
      ·
        refine ⟨73640537196434390069175667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98187382928579186758900889 73640537196434390069175667)
        ·
          refine ⟨110460805794651585103763501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73640537196434390069175667 110460805794651585103763501)
          ·
            refine ⟨41422802172994344413911313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110460805794651585103763501 41422802172994344413911313)
            ·
              refine ⟨31067101629745758310433485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41422802172994344413911313 31067101629745758310433485)
              ·
                refine ⟨11650163111154659366412557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31067101629745758310433485 11650163111154659366412557)
                ·
                  refine ⟨4368811166682997262404709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11650163111154659366412557 4368811166682997262404709)
                  ·
                    refine ⟨819152093753061986700883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4368811166682997262404709 819152093753061986700883)
                    ·
                      rfl

theorem cell23_4785879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_4785879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785879 prefixEnd_4785879 := by exact prefixLift 4785879
  have htrace : WordTrace (prefixWord ++ tailWord_4785879) baseStart_4785879 baseEnd_4785879 := by
    simpa [prefixWord, tailWord_4785879, baseEnd_4785879] using wordTrace_append hprefix tailTrace_4785879
  have hstable : (prefixWord ++ tailWord_4785879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785879).length < 2 ^ (prefixWord ++ tailWord_4785879).sum := by decide
  have hdescent : baseEnd_4785879 < baseStart_4785879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785896 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 3, 4]
def baseStart_4785896 : Nat := 118140960795 + 4785896 * 2 ^ 59
def prefixEnd_4785896 : Nat := 4983230072969 + 3 ^ 40 * 4785896 * 2
def baseEnd_4785896 : Nat := 819155003476770797863357

theorem tailTrace_4785896 : CollatzResearch.WordTrace tailWord_4785896 prefixEnd_4785896 819155003476770797863357 := by
  unfold tailWord_4785896
  simp only [CollatzResearch.WordTrace]
  refine ⟨87277983734761816404040771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116370644979682421872054361 87277983734761816404040771)
  ·
    refine ⟨130916975602142724606061157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87277983734761816404040771 130916975602142724606061157)
    ·
      refine ⟨24546932925401760863636467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130916975602142724606061157 24546932925401760863636467)
      ·
        refine ⟨36820399388102641295454701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24546932925401760863636467 36820399388102641295454701)
        ·
          refine ⟨13807649770538490485795513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36820399388102641295454701 13807649770538490485795513)
          ·
            refine ⟨10355737327903867864346635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13807649770538490485795513 10355737327903867864346635)
            ·
              refine ⟨15533605991855801796519953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10355737327903867864346635 15533605991855801796519953)
              ·
                refine ⟨11650204493891851347389965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15533605991855801796519953 11650204493891851347389965)
                ·
                  refine ⟨4368826685209444255271237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11650204493891851347389965 4368826685209444255271237)
                  ·
                    refine ⟨819155003476770797863357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4368826685209444255271237 819155003476770797863357)
                    ·
                      rfl

theorem cell23_4785896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_4785896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785896 prefixEnd_4785896 := by exact prefixLift 4785896
  have htrace : WordTrace (prefixWord ++ tailWord_4785896) baseStart_4785896 baseEnd_4785896 := by
    simpa [prefixWord, tailWord_4785896, baseEnd_4785896] using wordTrace_append hprefix tailTrace_4785896
  have hstable : (prefixWord ++ tailWord_4785896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785896).length < 2 ^ (prefixWord ++ tailWord_4785896).sum := by decide
  have hdescent : baseEnd_4785896 < baseStart_4785896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785946 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2]
def baseStart_4785946 : Nat := 118140960795 + 4785946 * 2 ^ 59
def prefixEnd_4785946 : Nat := 4983230072969 + 3 ^ 40 * 4785946 * 2
def baseEnd_4785946 : Nat := 2457490684463037197964841

theorem tailTrace_4785946 : CollatzResearch.WordTrace tailWord_4785946 prefixEnd_4785946 2457490684463037197964841 := by
  unfold tailWord_4785946
  simp only [CollatzResearch.WordTrace]
  refine ⟨43639447779835622836850423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116371860746228327564934461 43639447779835622836850423)
  ·
    refine ⟨65459171669753434255275635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43639447779835622836850423 65459171669753434255275635)
    ·
      refine ⟨98188757504630151382913453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65459171669753434255275635 98188757504630151382913453)
      ·
        refine ⟨36820784064236306768592545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98188757504630151382913453 36820784064236306768592545)
        ·
          refine ⟨27615588048177230076444409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36820784064236306768592545 27615588048177230076444409)
          ·
            refine ⟨20711691036132922557333307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27615588048177230076444409 20711691036132922557333307)
            ·
              refine ⟨31067536554199383835999961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20711691036132922557333307 31067536554199383835999961)
              ·
                refine ⟨23300652415649537876999971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31067536554199383835999961 23300652415649537876999971)
                ·
                  refine ⟨34950978623474306815499957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23300652415649537876999971 34950978623474306815499957)
                  ·
                    refine ⟨3276654245950716263953121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34950978623474306815499957 3276654245950716263953121)
                    ·
                      refine ⟨2457490684463037197964841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276654245950716263953121 2457490684463037197964841)
                      ·
                        rfl

theorem cell23_4785946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_4785946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785946 prefixEnd_4785946 := by exact prefixLift 4785946
  have htrace : WordTrace (prefixWord ++ tailWord_4785946) baseStart_4785946 baseEnd_4785946 := by
    simpa [prefixWord, tailWord_4785946, baseEnd_4785946] using wordTrace_append hprefix tailTrace_4785946
  have hstable : (prefixWord ++ tailWord_4785946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785946).length < 2 ^ (prefixWord ++ tailWord_4785946).sum := by decide
  have hdescent : baseEnd_4785946 < baseStart_4785946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785956 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_4785956 : Nat := 118140960795 + 4785956 * 2 ^ 59
def prefixEnd_4785956 : Nat := 4983230072969 + 3 ^ 40 * 4785956 * 2
def baseEnd_4785956 : Nat := 819165273089860719613265

theorem tailTrace_4785956 : CollatzResearch.WordTrace tailWord_4785956 prefixEnd_4785956 819165273089860719613265 := by
  unfold tailWord_4785956
  simp only [CollatzResearch.WordTrace]
  refine ⟨87279077924653131527632861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116372103899537508703510481 87279077924653131527632861)
  ·
    refine ⟨32729654221744924322862323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87279077924653131527632861 32729654221744924322862323)
    ·
      refine ⟨49094481332617386484293485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32729654221744924322862323 49094481332617386484293485)
      ·
        refine ⟨18410430499731519931610057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49094481332617386484293485 18410430499731519931610057)
        ·
          refine ⟨13807822874798639948707543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18410430499731519931610057 13807822874798639948707543)
          ·
            refine ⟨20711734312197959923061315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13807822874798639948707543 20711734312197959923061315)
            ·
              refine ⟨31067601468296939884591973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20711734312197959923061315 31067601468296939884591973)
              ·
                refine ⟨5825175275305676228360995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31067601468296939884591973 5825175275305676228360995)
                ·
                  refine ⟨8737762912958514342541493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5825175275305676228360995 8737762912958514342541493)
                  ·
                    refine ⟨819165273089860719613265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8737762912958514342541493 819165273089860719613265)
                    ·
                      rfl

theorem cell23_4785956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_4785956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785956 prefixEnd_4785956 := by exact prefixLift 4785956
  have htrace : WordTrace (prefixWord ++ tailWord_4785956) baseStart_4785956 baseEnd_4785956 := by
    simpa [prefixWord, tailWord_4785956, baseEnd_4785956] using wordTrace_append hprefix tailTrace_4785956
  have hstable : (prefixWord ++ tailWord_4785956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785956).length < 2 ^ (prefixWord ++ tailWord_4785956).sum := by decide
  have hdescent : baseEnd_4785956 < baseStart_4785956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785970 : List Nat := [3, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_4785970 : Nat := 118140960795 + 4785970 * 2 ^ 59
def prefixEnd_4785970 : Nat := 4983230072969 + 3 ^ 40 * 4785970 * 2
def baseEnd_4785970 : Nat := 2457503007998745104064731

theorem tailTrace_4785970 : CollatzResearch.WordTrace tailWord_4785970 prefixEnd_4785970 2457503007998745104064731 := by
  unfold tailWord_4785970
  simp only [CollatzResearch.WordTrace]
  refine ⟨43639666617813885861568841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116372444314170362297516909 43639666617813885861568841)
  ·
    refine ⟨32729749963360414396176631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43639666617813885861568841 32729749963360414396176631)
    ·
      refine ⟨49094624945040621594264947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32729749963360414396176631 49094624945040621594264947)
      ·
        refine ⟨73641937417560932391397421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49094624945040621594264947 73641937417560932391397421)
        ·
          refine ⟨27615726531585349646774033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73641937417560932391397421 27615726531585349646774033)
          ·
            refine ⟨20711794898689012235080525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27615726531585349646774033 20711794898689012235080525)
            ·
              refine ⟨7766923087008379588155197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20711794898689012235080525 7766923087008379588155197)
              ·
                refine ⟨2912596157628142345558199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7766923087008379588155197 2912596157628142345558199)
                ·
                  refine ⟨4368894236442213518337299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912596157628142345558199 4368894236442213518337299)
                  ·
                    refine ⟨6553341354663320277505949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4368894236442213518337299 6553341354663320277505949)
                    ·
                      refine ⟨2457503007998745104064731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553341354663320277505949 2457503007998745104064731)
                      ·
                        rfl

theorem cell23_4785970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_4785970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785970 prefixEnd_4785970 := by exact prefixLift 4785970
  have htrace : WordTrace (prefixWord ++ tailWord_4785970) baseStart_4785970 baseEnd_4785970 := by
    simpa [prefixWord, tailWord_4785970, baseEnd_4785970] using wordTrace_append hprefix tailTrace_4785970
  have hstable : (prefixWord ++ tailWord_4785970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785970).length < 2 ^ (prefixWord ++ tailWord_4785970).sum := by decide
  have hdescent : baseEnd_4785970 < baseStart_4785970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785976 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_4785976 : Nat := 118140960795 + 4785976 * 2 ^ 59
def prefixEnd_4785976 : Nat := 4983230072969 + 3 ^ 40 * 4785976 * 2
def baseEnd_4785976 : Nat := 2457506088882672080589703

theorem tailTrace_4785976 : CollatzResearch.WordTrace tailWord_4785976 prefixEnd_4785976 2457506088882672080589703 := by
  unfold tailWord_4785976
  simp only [CollatzResearch.WordTrace]
  refine ⟨87279442654616903235496891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116372590206155870980662521 87279442654616903235496891)
  ·
    refine ⟨130919163981925354853245337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87279442654616903235496891 130919163981925354853245337)
    ·
      refine ⟨98189372986444016139934003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130919163981925354853245337 98189372986444016139934003)
      ·
        refine ⟨147284059479666024209901005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98189372986444016139934003 147284059479666024209901005)
        ·
          refine ⟨55231522304874759078712877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147284059479666024209901005 55231522304874759078712877)
          ·
            refine ⟨20711820864328034654517329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55231522304874759078712877 20711820864328034654517329)
            ·
              refine ⟨15533865648246025990887997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20711820864328034654517329 15533865648246025990887997)
              ·
                refine ⟨5825199618092259746582999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15533865648246025990887997 5825199618092259746582999)
                ·
                  refine ⟨8737799427138389619874499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5825199618092259746582999 8737799427138389619874499)
                  ·
                    refine ⟨13106699140707584429811749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8737799427138389619874499 13106699140707584429811749)
                    ·
                      refine ⟨2457506088882672080589703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13106699140707584429811749 2457506088882672080589703)
                      ·
                        rfl

theorem cell23_4785976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_4785976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785976 prefixEnd_4785976 := by exact prefixLift 4785976
  have htrace : WordTrace (prefixWord ++ tailWord_4785976) baseStart_4785976 baseEnd_4785976 := by
    simpa [prefixWord, tailWord_4785976, baseEnd_4785976] using wordTrace_append hprefix tailTrace_4785976
  have hstable : (prefixWord ++ tailWord_4785976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785976).length < 2 ^ (prefixWord ++ tailWord_4785976).sum := by decide
  have hdescent : baseEnd_4785976 < baseStart_4785976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786083 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 4, 2, 2]
def baseStart_4786083 : Nat := 118140960795 + 4786083 * 2 ^ 59
def prefixEnd_4786083 : Nat := 4983230072969 + 3 ^ 40 * 4786083 * 2
def baseEnd_4786083 : Nat := 2457561031312703161951711

theorem tailTrace_4786083 : CollatzResearch.WordTrace tailWord_4786083 prefixEnd_4786083 2457561031312703161951711 := by
  unfold tailWord_4786083
  simp only [CollatzResearch.WordTrace]
  refine ⟨174562787919846163745138903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116375191946564109163425935 174562787919846163745138903)
  ·
    refine ⟨261844181879769245617708355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174562787919846163745138903 261844181879769245617708355)
    ·
      refine ⟨392766272819653868426562533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261844181879769245617708355 392766272819653868426562533)
      ·
        refine ⟨73643676153685100329980475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 392766272819653868426562533 73643676153685100329980475)
        ·
          refine ⟨110465514230527650494970713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73643676153685100329980475 110465514230527650494970713)
          ·
            refine ⟨82849135672895737871228035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110465514230527650494970713 82849135672895737871228035)
            ·
              refine ⟨124273703509343606806842053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82849135672895737871228035 124273703509343606806842053)
              ·
                refine ⟨23301319408001926276282885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124273703509343606806842053 23301319408001926276282885)
                ·
                  refine ⟨4368997389000361176803041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23301319408001926276282885 4368997389000361176803041)
                  ·
                    refine ⟨3276748041750270882602281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4368997389000361176803041 3276748041750270882602281)
                    ·
                      refine ⟨2457561031312703161951711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276748041750270882602281 2457561031312703161951711)
                      ·
                        rfl

theorem cell23_4786083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_4786083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786083 prefixEnd_4786083 := by exact prefixLift 4786083
  have htrace : WordTrace (prefixWord ++ tailWord_4786083) baseStart_4786083 baseEnd_4786083 := by
    simpa [prefixWord, tailWord_4786083, baseEnd_4786083] using wordTrace_append hprefix tailTrace_4786083
  have hstable : (prefixWord ++ tailWord_4786083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786083).length < 2 ^ (prefixWord ++ tailWord_4786083).sum := by decide
  have hdescent : baseEnd_4786083 < baseStart_4786083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786087 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_4786087 : Nat := 118140960795 + 4786087 * 2 ^ 59
def prefixEnd_4786087 : Nat := 4983230072969 + 3 ^ 40 * 4786087 * 2
def baseEnd_4786087 : Nat := 2457563085235321146301693

theorem tailTrace_4786087 : CollatzResearch.WordTrace tailWord_4786087 prefixEnd_4786087 2457563085235321146301693 := by
  unfold tailWord_4786087
  simp only [CollatzResearch.WordTrace]
  refine ⟨174562933811831672428284515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116375289207887781618856343 174562933811831672428284515)
  ·
    refine ⟨261844400717747508642426773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174562933811831672428284515 261844400717747508642426773)
    ·
      refine ⟨12273956283644414467613755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 261844400717747508642426773 12273956283644414467613755)
      ·
        refine ⟨18410934425466621701420633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12273956283644414467613755 18410934425466621701420633)
        ·
          refine ⟨13808200819099966276065475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18410934425466621701420633 13808200819099966276065475)
          ·
            refine ⟨20712301228649949414098213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13808200819099966276065475 20712301228649949414098213)
            ·
              refine ⟨3883556480371865515143415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20712301228649949414098213 3883556480371865515143415)
              ·
                refine ⟨5825334720557798272715123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3883556480371865515143415 5825334720557798272715123)
                ·
                  refine ⟨8738002080836697409072685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5825334720557798272715123 8738002080836697409072685)
                  ·
                    refine ⟨3276750780313761528402257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8738002080836697409072685 3276750780313761528402257)
                    ·
                      refine ⟨2457563085235321146301693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276750780313761528402257 2457563085235321146301693)
                      ·
                        rfl

theorem cell23_4786087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_4786087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786087 prefixEnd_4786087 := by exact prefixLift 4786087
  have htrace : WordTrace (prefixWord ++ tailWord_4786087) baseStart_4786087 baseEnd_4786087 := by
    simpa [prefixWord, tailWord_4786087, baseEnd_4786087] using wordTrace_append hprefix tailTrace_4786087
  have hstable : (prefixWord ++ tailWord_4786087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786087).length < 2 ^ (prefixWord ++ tailWord_4786087).sum := by decide
  have hdescent : baseEnd_4786087 < baseStart_4786087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786094 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4786094 : Nat := 118140960795 + 4786094 * 2 ^ 59
def prefixEnd_4786094 : Nat := 4983230072969 + 3 ^ 40 * 4786094 * 2
def baseEnd_4786094 : Nat := 2457566679599902618914161

theorem tailTrace_4786094 : CollatzResearch.WordTrace tailWord_4786094 prefixEnd_4786094 2457566679599902618914161 := by
  unfold tailWord_4786094
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820398640350789077973667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116375459415204208415859557 21820398640350789077973667)
  ·
    refine ⟨32730597960526183616960501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21820398640350789077973667 32730597960526183616960501)
    ·
      refine ⟨3068493558799329714090047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32730597960526183616960501 3068493558799329714090047)
      ·
        refine ⟨4602740338198994571135071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068493558799329714090047 4602740338198994571135071)
        ·
          refine ⟨6904110507298491856702607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602740338198994571135071 6904110507298491856702607)
          ·
            refine ⟨10356165760947737785053911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904110507298491856702607 10356165760947737785053911)
            ·
              refine ⟨15534248641421606677580867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10356165760947737785053911 15534248641421606677580867)
              ·
                refine ⟨23301372962132410016371301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15534248641421606677580867 23301372962132410016371301)
                ·
                  refine ⟨4369007430399826878069619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23301372962132410016371301 4369007430399826878069619)
                  ·
                    refine ⟨6553511145599740317104429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369007430399826878069619 6553511145599740317104429)
                    ·
                      refine ⟨2457566679599902618914161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553511145599740317104429 2457566679599902618914161)
                      ·
                        rfl

theorem cell23_4786094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4786094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786094 prefixEnd_4786094 := by exact prefixLift 4786094
  have htrace : WordTrace (prefixWord ++ tailWord_4786094) baseStart_4786094 baseEnd_4786094 := by
    simpa [prefixWord, tailWord_4786094, baseEnd_4786094] using wordTrace_append hprefix tailTrace_4786094
  have hstable : (prefixWord ++ tailWord_4786094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786094).length < 2 ^ (prefixWord ++ tailWord_4786094).sum := by decide
  have hdescent : baseEnd_4786094 < baseStart_4786094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786129 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_4786129 : Nat := 118140960795 + 4786129 * 2 ^ 59
def prefixEnd_4786129 : Nat := 4983230072969 + 3 ^ 40 * 4786129 * 2
def baseEnd_4786129 : Nat := 2457584651422809981976499

theorem tailTrace_4786129 : CollatzResearch.WordTrace tailWord_4786129 prefixEnd_4786129 2457584651422809981976499 := by
  unfold tailWord_4786129
  simp only [CollatzResearch.WordTrace]
  refine ⟨174564465677679513601313441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116376310451786342400875627 174564465677679513601313441)
  ·
    refine ⟨130923349258259635200985081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174564465677679513601313441 130923349258259635200985081)
    ·
      refine ⟨98192511943694726400738811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130923349258259635200985081 98192511943694726400738811)
      ·
        refine ⟨147288767915542089601108217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98192511943694726400738811 147288767915542089601108217)
        ·
          refine ⟨110466575936656567200831163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147288767915542089601108217 110466575936656567200831163)
          ·
            refine ⟨165699863904984850801246745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110466575936656567200831163 165699863904984850801246745)
            ·
              refine ⟨124274897928738638100935059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165699863904984850801246745 124274897928738638100935059)
              ·
                refine ⟨186412346893107957151402589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124274897928738638100935059 186412346893107957151402589)
                ·
                  refine ⟨69904630084915483931775971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186412346893107957151402589 69904630084915483931775971)
                  ·
                    refine ⟨104856945127373225897663957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69904630084915483931775971 104856945127373225897663957)
                    ·
                      refine ⟨2457584651422809981976499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104856945127373225897663957 2457584651422809981976499)
                      ·
                        rfl

theorem cell23_4786129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_4786129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786129 prefixEnd_4786129 := by exact prefixLift 4786129
  have htrace : WordTrace (prefixWord ++ tailWord_4786129) baseStart_4786129 baseEnd_4786129 := by
    simpa [prefixWord, tailWord_4786129, baseEnd_4786129] using wordTrace_append hprefix tailTrace_4786129
  have hstable : (prefixWord ++ tailWord_4786129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786129).length < 2 ^ (prefixWord ++ tailWord_4786129).sum := by decide
  have hdescent : baseEnd_4786129 < baseStart_4786129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786136 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 2, 5]
def baseStart_4786136 : Nat := 118140960795 + 4786136 * 2 ^ 59
def prefixEnd_4786136 : Nat := 4983230072969 + 3 ^ 40 * 4786136 * 2
def baseEnd_4786136 : Nat := 819196081929130484862989

theorem tailTrace_4786136 : CollatzResearch.WordTrace tailWord_4786136 prefixEnd_4786136 819196081929130484862989 := by
  unfold tailWord_4786136
  simp only [CollatzResearch.WordTrace]
  refine ⟨87282360494327076898409131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116376480659102769197878841 87282360494327076898409131)
  ·
    refine ⟨130923540741490615347613697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87282360494327076898409131 130923540741490615347613697)
    ·
      refine ⟨98192655556117961510710273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130923540741490615347613697 98192655556117961510710273)
      ·
        refine ⟨73644491667088471133032705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98192655556117961510710273 73644491667088471133032705)
        ·
          refine ⟨55233368750316353349774529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73644491667088471133032705 55233368750316353349774529)
          ·
            refine ⟨41425026562737265012330897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55233368750316353349774529 41425026562737265012330897)
            ·
              refine ⟨31068769922052948759248173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41425026562737265012330897 31068769922052948759248173)
              ·
                refine ⟨11650788720769855784718065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31068769922052948759248173 11650788720769855784718065)
                ·
                  refine ⟨8738091540577391838538549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11650788720769855784718065 8738091540577391838538549)
                  ·
                    refine ⟨819196081929130484862989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8738091540577391838538549 819196081929130484862989)
                    ·
                      rfl

theorem cell23_4786136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_4786136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786136 prefixEnd_4786136 := by exact prefixLift 4786136
  have htrace : WordTrace (prefixWord ++ tailWord_4786136) baseStart_4786136 baseEnd_4786136 := by
    simpa [prefixWord, tailWord_4786136, baseEnd_4786136] using wordTrace_append hprefix tailTrace_4786136
  have hstable : (prefixWord ++ tailWord_4786136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786136).length < 2 ^ (prefixWord ++ tailWord_4786136).sum := by decide
  have hdescent : baseEnd_4786136 < baseStart_4786136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786157 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 7]
def baseStart_4786157 : Nat := 118140960795 + 4786157 * 2 ^ 59
def prefixEnd_4786157 : Nat := 4983230072969 + 3 ^ 40 * 4786157 * 2
def baseEnd_4786157 : Nat := 273066558764570652491819

theorem tailTrace_4786157 : CollatzResearch.WordTrace tailWord_4786157 prefixEnd_4786157 273066558764570652491819 := by
  unfold tailWord_4786157
  simp only [CollatzResearch.WordTrace]
  refine ⟨174565486921578074383332725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116376991281052049588888483 174565486921578074383332725)
  ·
    refine ⟨16365514398897944473437443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174565486921578074383332725 16365514398897944473437443)
    ·
      refine ⟨24548271598346916710156165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16365514398897944473437443 24548271598346916710156165)
      ·
        refine ⟨4602800924690046883154281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24548271598346916710156165 4602800924690046883154281)
        ·
          refine ⟨3452100693517535162365711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4602800924690046883154281 3452100693517535162365711)
          ·
            refine ⟨5178151040276302743548567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452100693517535162365711 5178151040276302743548567)
            ·
              refine ⟨7767226560414454115322851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5178151040276302743548567 7767226560414454115322851)
              ·
                refine ⟨11650839840621681172984277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7767226560414454115322851 11650839840621681172984277)
                ·
                  refine ⟨273066558764570652491819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11650839840621681172984277 273066558764570652491819)
                  ·
                    rfl

theorem cell23_4786157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_4786157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786157 prefixEnd_4786157 := by exact prefixLift 4786157
  have htrace : WordTrace (prefixWord ++ tailWord_4786157) baseStart_4786157 baseEnd_4786157 := by
    simpa [prefixWord, tailWord_4786157, baseEnd_4786157] using wordTrace_append hprefix tailTrace_4786157
  have hstable : (prefixWord ++ tailWord_4786157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786157).length < 2 ^ (prefixWord ++ tailWord_4786157).sum := by decide
  have hdescent : baseEnd_4786157 < baseStart_4786157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786173 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_4786173 : Nat := 118140960795 + 4786173 * 2 ^ 59
def prefixEnd_4786173 : Nat := 4983230072969 + 3 ^ 40 * 4786173 * 2
def baseEnd_4786173 : Nat := 2457607244571607809826297

theorem tailTrace_4786173 : CollatzResearch.WordTrace tailWord_4786173 prefixEnd_4786173 2457607244571607809826297 := by
  unfold tailWord_4786173
  simp only [CollatzResearch.WordTrace]
  refine ⟨174566070489520109115915173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116377380326346739410610115 174566070489520109115915173)
  ·
    refine ⟨32731138216785020459234095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174566070489520109115915173 32731138216785020459234095)
    ·
      refine ⟨49096707325177530688851143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32731138216785020459234095 49096707325177530688851143)
      ·
        refine ⟨73645060987766296033276715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49096707325177530688851143 73645060987766296033276715)
        ·
          refine ⟨110467591481649444049915073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73645060987766296033276715 110467591481649444049915073)
          ·
            refine ⟨82850693611237083037436305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110467591481649444049915073 82850693611237083037436305)
            ·
              refine ⟨62138020208427812278077229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82850693611237083037436305 62138020208427812278077229)
              ·
                refine ⟨23301757578160429604278961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62138020208427812278077229 23301757578160429604278961)
                ·
                  refine ⟨17476318183620322203209221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23301757578160429604278961 17476318183620322203209221)
                  ·
                    refine ⟨3276809659428810413101729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17476318183620322203209221 3276809659428810413101729)
                    ·
                      refine ⟨2457607244571607809826297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276809659428810413101729 2457607244571607809826297)
                      ·
                        rfl

theorem cell23_4786173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_4786173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786173 prefixEnd_4786173 := by exact prefixLift 4786173
  have htrace : WordTrace (prefixWord ++ tailWord_4786173) baseStart_4786173 baseEnd_4786173 := by
    simpa [prefixWord, tailWord_4786173, baseEnd_4786173] using wordTrace_append hprefix tailTrace_4786173
  have hstable : (prefixWord ++ tailWord_4786173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786173).length < 2 ^ (prefixWord ++ tailWord_4786173).sum := by decide
  have hdescent : baseEnd_4786173 < baseStart_4786173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786176 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3]
def baseStart_4786176 : Nat := 118140960795 + 4786176 * 2 ^ 59
def prefixEnd_4786176 : Nat := 4983230072969 + 3 ^ 40 * 4786176 * 2
def baseEnd_4786176 : Nat := 2457608785013571298088783

theorem tailTrace_4786176 : CollatzResearch.WordTrace tailWord_4786176 prefixEnd_4786176 2457608785013571298088783 := by
  unfold tailWord_4786176
  simp only [CollatzResearch.WordTrace]
  refine ⟨87283089954254620314137191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116377453272339493752182921 87283089954254620314137191)
  ·
    refine ⟨130924634931381930471205787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87283089954254620314137191 130924634931381930471205787)
    ·
      refine ⟨196386952397072895706808681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130924634931381930471205787 196386952397072895706808681)
      ·
        refine ⟨147290214297804671780106511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196386952397072895706808681 147290214297804671780106511)
        ·
          refine ⟨220935321446707007670159767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147290214297804671780106511 220935321446707007670159767)
          ·
            refine ⟨331402982170060511505239651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220935321446707007670159767 331402982170060511505239651)
            ·
              refine ⟨497104473255090767257859477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331402982170060511505239651 497104473255090767257859477)
              ·
                refine ⟨23301772183832379715212163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 497104473255090767257859477 23301772183832379715212163)
                ·
                  refine ⟨34952658275748569572818245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23301772183832379715212163 34952658275748569572818245)
                  ·
                    refine ⟨6553623426702856794903421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34952658275748569572818245 6553623426702856794903421)
                    ·
                      refine ⟨2457608785013571298088783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553623426702856794903421 2457608785013571298088783)
                      ·
                        rfl

theorem cell23_4786176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_4786176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786176 prefixEnd_4786176 := by exact prefixLift 4786176
  have htrace : WordTrace (prefixWord ++ tailWord_4786176) baseStart_4786176 baseEnd_4786176 := by
    simpa [prefixWord, tailWord_4786176, baseEnd_4786176] using wordTrace_append hprefix tailTrace_4786176
  have hstable : (prefixWord ++ tailWord_4786176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786176).length < 2 ^ (prefixWord ++ tailWord_4786176).sum := by decide
  have hdescent : baseEnd_4786176 < baseStart_4786176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786200 : List Nat := [2, 1, 2, 3, 2, 1, 2, 5, 1, 4]
def baseStart_4786200 : Nat := 118140960795 + 4786200 * 2 ^ 59
def prefixEnd_4786200 : Nat := 4983230072969 + 3 ^ 40 * 4786200 * 2
def baseEnd_4786200 : Nat := 819207036183093068062891

theorem tailTrace_4786200 : CollatzResearch.WordTrace tailWord_4786200 prefixEnd_4786200 819207036183093068062891 := by
  unfold tailWord_4786200
  simp only [CollatzResearch.WordTrace]
  refine ⟨87283527630211146363574027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116378036840281528484765369 87283527630211146363574027)
  ·
    refine ⟨130925291445316719545361041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87283527630211146363574027 130925291445316719545361041)
    ·
      refine ⟨98193968583987539659020781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130925291445316719545361041 98193968583987539659020781)
      ·
        refine ⟨36822738218995327372132793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98193968583987539659020781 36822738218995327372132793)
        ·
          refine ⟨27617053664246495529099595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36822738218995327372132793 27617053664246495529099595)
          ·
            refine ⟨41425580496369743293649393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27617053664246495529099595 41425580496369743293649393)
            ·
              refine ⟨31069185372277307470237045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41425580496369743293649393 31069185372277307470237045)
              ·
                refine ⟨2912736128650997575334723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31069185372277307470237045 2912736128650997575334723)
                ·
                  refine ⟨4369104192976496363002085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912736128650997575334723 4369104192976496363002085)
                  ·
                    refine ⟨819207036183093068062891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369104192976496363002085 819207036183093068062891)
                    ·
                      rfl

theorem cell23_4786200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_4786200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786200 prefixEnd_4786200 := by exact prefixLift 4786200
  have htrace : WordTrace (prefixWord ++ tailWord_4786200) baseStart_4786200 baseEnd_4786200 := by
    simpa [prefixWord, tailWord_4786200, baseEnd_4786200] using wordTrace_append hprefix tailTrace_4786200
  have hstable : (prefixWord ++ tailWord_4786200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786200).length < 2 ^ (prefixWord ++ tailWord_4786200).sum := by decide
  have hdescent : baseEnd_4786200 < baseStart_4786200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786213 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 6]
def baseStart_4786213 : Nat := 118140960795 + 4786213 * 2 ^ 59
def prefixEnd_4786213 : Nat := 4983230072969 + 3 ^ 40 * 4786213 * 2
def baseEnd_4786213 : Nat := 273069753755309739258457

theorem tailTrace_4786213 : CollatzResearch.WordTrace tailWord_4786213 prefixEnd_4786213 273069753755309739258457 := by
  unfold tailWord_4786213
  simp only [CollatzResearch.WordTrace]
  refine ⟨174567529409375195947371293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116378352939583463964914195 174567529409375195947371293)
  ·
    refine ⟨65462823528515698480264235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174567529409375195947371293 65462823528515698480264235)
    ·
      refine ⟨98194235292773547720396353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65462823528515698480264235 98194235292773547720396353)
      ·
        refine ⟨73645676469580160790297265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98194235292773547720396353 73645676469580160790297265)
        ·
          refine ⟨55234257352185120592722949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73645676469580160790297265 55234257352185120592722949)
          ·
            refine ⟨10356423253534710111135553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55234257352185120592722949 10356423253534710111135553)
            ·
              refine ⟨7767317440151032583351665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10356423253534710111135553 7767317440151032583351665)
              ·
                refine ⟨5825488080113274437513749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7767317440151032583351665 5825488080113274437513749)
                ·
                  refine ⟨273069753755309739258457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5825488080113274437513749 273069753755309739258457)
                  ·
                    rfl

theorem cell23_4786213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_4786213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786213 prefixEnd_4786213 := by exact prefixLift 4786213
  have htrace : WordTrace (prefixWord ++ tailWord_4786213) baseStart_4786213 baseEnd_4786213 := by
    simpa [prefixWord, tailWord_4786213, baseEnd_4786213] using wordTrace_append hprefix tailTrace_4786213
  have hstable : (prefixWord ++ tailWord_4786213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786213).length < 2 ^ (prefixWord ++ tailWord_4786213).sum := by decide
  have hdescent : baseEnd_4786213 < baseStart_4786213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786236 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_4786236 : Nat := 118140960795 + 4786236 * 2 ^ 59
def prefixEnd_4786236 : Nat := 4983230072969 + 3 ^ 40 * 4786236 * 2
def baseEnd_4786236 : Nat := 2457639593852841063338507

theorem tailTrace_4786236 : CollatzResearch.WordTrace tailWord_4786236 prefixEnd_4786236 2457639593852841063338507 := by
  unfold tailWord_4786236
  simp only [CollatzResearch.WordTrace]
  refine ⟨87284184144145935437729281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116378912192194580583639041 87284184144145935437729281)
  ·
    refine ⟨65463138108109451578296961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87284184144145935437729281 65463138108109451578296961)
    ·
      refine ⟨49097353581082088683722721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65463138108109451578296961 49097353581082088683722721)
      ·
        refine ⟨36823015185811566512792041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49097353581082088683722721 36823015185811566512792041)
        ·
          refine ⟨27617261389358674884594031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36823015185811566512792041 27617261389358674884594031)
          ·
            refine ⟨41425892084038012326891047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27617261389358674884594031 41425892084038012326891047)
            ·
              refine ⟨62138838126057018490336571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41425892084038012326891047 62138838126057018490336571)
              ·
                refine ⟨93208257189085527735504857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62138838126057018490336571 93208257189085527735504857)
                ·
                  refine ⟨69906192891814145801628643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93208257189085527735504857 69906192891814145801628643)
                  ·
                    refine ⟨104859289337721218702442965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69906192891814145801628643 104859289337721218702442965)
                    ·
                      refine ⟨2457639593852841063338507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104859289337721218702442965 2457639593852841063338507)
                      ·
                        rfl

theorem cell23_4786236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_4786236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786236 prefixEnd_4786236 := by exact prefixLift 4786236
  have htrace : WordTrace (prefixWord ++ tailWord_4786236) baseStart_4786236 baseEnd_4786236 := by
    simpa [prefixWord, tailWord_4786236, baseEnd_4786236] using wordTrace_append hprefix tailTrace_4786236
  have hstable : (prefixWord ++ tailWord_4786236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786236).length < 2 ^ (prefixWord ++ tailWord_4786236).sum := by decide
  have hdescent : baseEnd_4786236 < baseStart_4786236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786240 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 3, 1, 3]
def baseStart_4786240 : Nat := 118140960795 + 4786240 * 2 ^ 59
def prefixEnd_4786240 : Nat := 4983230072969 + 3 ^ 40 * 4786240 * 2
def baseEnd_4786240 : Nat := 2457641647775459047688489

theorem tailTrace_4786240 : CollatzResearch.WordTrace tailWord_4786240 prefixEnd_4786240 2457641647775459047688489 := by
  unfold tailWord_4786240
  simp only [CollatzResearch.WordTrace]
  refine ⟨87284257090138689779302087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116379009453518253039069449 87284257090138689779302087)
  ·
    refine ⟨130926385635208034668953131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87284257090138689779302087 130926385635208034668953131)
    ·
      refine ⟨196389578452812052003429697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130926385635208034668953131 196389578452812052003429697)
      ·
        refine ⟨147292183839609039002572273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196389578452812052003429697 147292183839609039002572273)
        ·
          refine ⟨110469137879706779251929205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147292183839609039002572273 110469137879706779251929205)
          ·
            refine ⟨10356481676222510554868363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110469137879706779251929205 10356481676222510554868363)
            ·
              refine ⟨15534722514333765832302545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10356481676222510554868363 15534722514333765832302545)
              ·
                refine ⟨11651041885750324374226909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15534722514333765832302545 11651041885750324374226909)
                ·
                  refine ⟨4369140707156371640335091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11651041885750324374226909 4369140707156371640335091)
                  ·
                    refine ⟨6553711060734557460502637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369140707156371640335091 6553711060734557460502637)
                    ·
                      refine ⟨2457641647775459047688489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553711060734557460502637 2457641647775459047688489)
                      ·
                        rfl

theorem cell23_4786240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_4786240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786240 prefixEnd_4786240 := by exact prefixLift 4786240
  have htrace : WordTrace (prefixWord ++ tailWord_4786240) baseStart_4786240 baseEnd_4786240 := by
    simpa [prefixWord, tailWord_4786240, baseEnd_4786240] using wordTrace_append hprefix tailTrace_4786240
  have hstable : (prefixWord ++ tailWord_4786240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786240).length < 2 ^ (prefixWord ++ tailWord_4786240).sum := by decide
  have hdescent : baseEnd_4786240 < baseStart_4786240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786274 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4786274 : Nat := 118140960795 + 4786274 * 2 ^ 59
def prefixEnd_4786274 : Nat := 4983230072969 + 3 ^ 40 * 4786274 * 2
def baseEnd_4786274 : Nat := 2457659106117711914663333

theorem tailTrace_4786274 : CollatzResearch.WordTrace tailWord_4786274 prefixEnd_4786274 2457659106117711914663333 := by
  unfold tailWord_4786274
  simp only [CollatzResearch.WordTrace]
  refine ⟨43642438565538550841335469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116379836174769468910227917 43642438565538550841335469)
  ·
    refine ⟨16365914462076956565500801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43642438565538550841335469 16365914462076956565500801)
    ·
      refine ⟨12274435846557717424125601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16365914462076956565500801 12274435846557717424125601)
      ·
        refine ⟨9205826884918288068094201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12274435846557717424125601 9205826884918288068094201)
        ·
          refine ⟨6904370163688716051070651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9205826884918288068094201 6904370163688716051070651)
          ·
            refine ⟨10356555245533074076605977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904370163688716051070651 10356555245533074076605977)
            ·
              refine ⟨7767416434149805557454483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10356555245533074076605977 7767416434149805557454483)
              ·
                refine ⟨11651124651224708336181725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7767416434149805557454483 11651124651224708336181725)
                ·
                  refine ⟨4369171744209265626068147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11651124651224708336181725 4369171744209265626068147)
                  ·
                    refine ⟨6553757616313898439102221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369171744209265626068147 6553757616313898439102221)
                    ·
                      refine ⟨2457659106117711914663333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553757616313898439102221 2457659106117711914663333)
                      ·
                        rfl

theorem cell23_4786274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4786274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786274 prefixEnd_4786274 := by exact prefixLift 4786274
  have htrace : WordTrace (prefixWord ++ tailWord_4786274) baseStart_4786274 baseEnd_4786274 := by
    simpa [prefixWord, tailWord_4786274, baseEnd_4786274] using wordTrace_append hprefix tailTrace_4786274
  have hstable : (prefixWord ++ tailWord_4786274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786274).length < 2 ^ (prefixWord ++ tailWord_4786274).sum := by decide
  have hdescent : baseEnd_4786274 < baseStart_4786274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786290 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_4786290 : Nat := 118140960795 + 4786290 * 2 ^ 59
def prefixEnd_4786290 : Nat := 4983230072969 + 3 ^ 40 * 4786290 * 2
def baseEnd_4786290 : Nat := 819222440602727950687753

theorem tailTrace_4786290 : CollatzResearch.WordTrace tailWord_4786290 prefixEnd_4786290 819222440602727950687753 := by
  unfold tailWord_4786290
  simp only [CollatzResearch.WordTrace]
  refine ⟨43642584457524059524481081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116380225220064158731949549 43642584457524059524481081)
  ·
    refine ⟨32731938343143044643360811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43642584457524059524481081 32731938343143044643360811)
    ·
      refine ⟨49097907514714566965041217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32731938343143044643360811 49097907514714566965041217)
      ·
        refine ⟨36823430636035925223780913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49097907514714566965041217 36823430636035925223780913)
        ·
          refine ⟨27617572977026943917835685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36823430636035925223780913 27617572977026943917835685)
          ·
            refine ⟨5178294933192551984594191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27617572977026943917835685 5178294933192551984594191)
            ·
              refine ⟨7767442399788827976891287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5178294933192551984594191 7767442399788827976891287)
              ·
                refine ⟨11651163599683241965336931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7767442399788827976891287 11651163599683241965336931)
                ·
                  refine ⟨17476745399524862948005397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11651163599683241965336931 17476745399524862948005397)
                  ·
                    refine ⟨819222440602727950687753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17476745399524862948005397 819222440602727950687753)
                    ·
                      rfl

theorem cell23_4786290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_4786290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786290 prefixEnd_4786290 := by exact prefixLift 4786290
  have htrace : WordTrace (prefixWord ++ tailWord_4786290) baseStart_4786290 baseEnd_4786290 := by
    simpa [prefixWord, tailWord_4786290, baseEnd_4786290] using wordTrace_append hprefix tailTrace_4786290
  have hstable : (prefixWord ++ tailWord_4786290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786290).length < 2 ^ (prefixWord ++ tailWord_4786290).sum := by decide
  have hdescent : baseEnd_4786290 < baseStart_4786290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786297 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 3, 2, 2]
def baseStart_4786297 : Nat := 118140960795 + 4786297 * 2 ^ 59
def prefixEnd_4786297 : Nat := 4983230072969 + 3 ^ 40 * 4786297 * 2
def baseEnd_4786297 : Nat := 2457670916172765324675727

theorem tailTrace_4786297 : CollatzResearch.WordTrace tailWord_4786297 prefixEnd_4786297 2457670916172765324675727 := by
  unfold tailWord_4786297
  simp only [CollatzResearch.WordTrace]
  refine ⟨174570593141070878293429145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116380395427380585528952763 174570593141070878293429145)
  ·
    refine ⟨130927944855803158720071859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174570593141070878293429145 130927944855803158720071859)
    ·
      refine ⟨196391917283704738080107789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130927944855803158720071859 196391917283704738080107789)
      ·
        refine ⟨73646968981389276780040421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196391917283704738080107789 73646968981389276780040421)
        ·
          refine ⟨13808806684010489396257579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73646968981389276780040421 13808806684010489396257579)
          ·
            refine ⟨20713210026015734094386369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13808806684010489396257579 20713210026015734094386369)
            ·
              refine ⟨15534907519511800570789777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20713210026015734094386369 15534907519511800570789777)
              ·
                refine ⟨11651180639633850428092333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15534907519511800570789777 11651180639633850428092333)
                ·
                  refine ⟨4369192739862693910534625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11651180639633850428092333 4369192739862693910534625)
                  ·
                    refine ⟨3276894554897020432900969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4369192739862693910534625 3276894554897020432900969)
                    ·
                      refine ⟨2457670916172765324675727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276894554897020432900969 2457670916172765324675727)
                      ·
                        rfl

theorem cell23_4786297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_4786297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786297 prefixEnd_4786297 := by exact prefixLift 4786297
  have htrace : WordTrace (prefixWord ++ tailWord_4786297) baseStart_4786297 baseEnd_4786297 := by
    simpa [prefixWord, tailWord_4786297, baseEnd_4786297] using wordTrace_append hprefix tailTrace_4786297
  have hstable : (prefixWord ++ tailWord_4786297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786297).length < 2 ^ (prefixWord ++ tailWord_4786297).sum := by decide
  have hdescent : baseEnd_4786297 < baseStart_4786297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786300 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_4786300 : Nat := 118140960795 + 4786300 * 2 ^ 59
def prefixEnd_4786300 : Nat := 4983230072969 + 3 ^ 40 * 4786300 * 2
def baseEnd_4786300 : Nat := 2457672456614728812938213

theorem tailTrace_4786300 : CollatzResearch.WordTrace tailWord_4786300 prefixEnd_4786300 2457672456614728812938213 := by
  unfold tailWord_4786300
  simp only [CollatzResearch.WordTrace]
  refine ⟨87285351280030004902894177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116380468373373339870525569 87285351280030004902894177)
  ·
    refine ⟨65464013460022503677170633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87285351280030004902894177 65464013460022503677170633)
    ·
      refine ⟨49098010095016877757877975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65464013460022503677170633 49098010095016877757877975)
      ·
        refine ⟨73647015142525316636816963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49098010095016877757877975 73647015142525316636816963)
        ·
          refine ⟨110470522713787974955225445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73647015142525316636816963 110470522713787974955225445)
          ·
            refine ⟨20713223008835245304104771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110470522713787974955225445 20713223008835245304104771)
            ·
              refine ⟨31069834513252867956157157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20713223008835245304104771 31069834513252867956157157)
              ·
                refine ⟨5825593971234912741779467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31069834513252867956157157 5825593971234912741779467)
                ·
                  refine ⟨8738390956852369112669201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5825593971234912741779467 8738390956852369112669201)
                  ·
                    refine ⟨6553793217639276834501901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8738390956852369112669201 6553793217639276834501901)
                    ·
                      refine ⟨2457672456614728812938213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553793217639276834501901 2457672456614728812938213)
                      ·
                        rfl

theorem cell23_4786300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_4786300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786300 prefixEnd_4786300 := by exact prefixLift 4786300
  have htrace : WordTrace (prefixWord ++ tailWord_4786300) baseStart_4786300 baseEnd_4786300 := by
    simpa [prefixWord, tailWord_4786300, baseEnd_4786300] using wordTrace_append hprefix tailTrace_4786300
  have hstable : (prefixWord ++ tailWord_4786300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786300).length < 2 ^ (prefixWord ++ tailWord_4786300).sum := by decide
  have hdescent : baseEnd_4786300 < baseStart_4786300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786313 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 3]
def baseStart_4786313 : Nat := 118140960795 + 4786313 * 2 ^ 59
def prefixEnd_4786313 : Nat := 4983230072969 + 3 ^ 40 * 4786313 * 2
def baseEnd_4786313 : Nat := 2457679131863237262075653

theorem tailTrace_4786313 : CollatzResearch.WordTrace tailWord_4786313 prefixEnd_4786313 2457679131863237262075653 := by
  unfold tailWord_4786313
  simp only [CollatzResearch.WordTrace]
  refine ⟨174571176709012913026011593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116380784472675275350674395 174571176709012913026011593)
  ·
    refine ⟨130928382531759684769508695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174571176709012913026011593 130928382531759684769508695)
    ·
      refine ⟨196392573797639527154263043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130928382531759684769508695 196392573797639527154263043)
      ·
        refine ⟨294588860696459290731394565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196392573797639527154263043 294588860696459290731394565)
        ·
          refine ⟨55235411380586117012136481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294588860696459290731394565 55235411380586117012136481)
          ·
            refine ⟨41426558535439587759102361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55235411380586117012136481 41426558535439587759102361)
            ·
              refine ⟨31069918901579690819326771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41426558535439587759102361 31069918901579690819326771)
              ·
                refine ⟨46604878352369536228990157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31069918901579690819326771 46604878352369536228990157)
                ·
                  refine ⟨17476829382138576085871309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46604878352369536228990157 17476829382138576085871309)
                  ·
                    refine ⟨6553811018301966032201741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17476829382138576085871309 6553811018301966032201741)
                    ·
                      refine ⟨2457679131863237262075653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6553811018301966032201741 2457679131863237262075653)
                      ·
                        rfl

theorem cell23_4786313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_4786313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786313 prefixEnd_4786313 := by exact prefixLift 4786313
  have htrace : WordTrace (prefixWord ++ tailWord_4786313) baseStart_4786313 baseEnd_4786313 := by
    simpa [prefixWord, tailWord_4786313, baseEnd_4786313] using wordTrace_append hprefix tailTrace_4786313
  have hstable : (prefixWord ++ tailWord_4786313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786313).length < 2 ^ (prefixWord ++ tailWord_4786313).sum := by decide
  have hdescent : baseEnd_4786313 < baseStart_4786313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786316 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_4786316 : Nat := 118140960795 + 4786316 * 2 ^ 59
def prefixEnd_4786316 : Nat := 4983230072969 + 3 ^ 40 * 4786316 * 2
def baseEnd_4786316 : Nat := 819226890768400250112713

theorem tailTrace_4786316 : CollatzResearch.WordTrace tailWord_4786316 prefixEnd_4786316 819226890768400250112713 := by
  unfold tailWord_4786316
  simp only [CollatzResearch.WordTrace]
  refine ⟨87285643064001022269185401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116380857418668029692247201 87285643064001022269185401)
  ·
    refine ⟨65464232298000766701889051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87285643064001022269185401 65464232298000766701889051)
    ·
      refine ⟨98196348447001150052833577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65464232298000766701889051 98196348447001150052833577)
      ·
        refine ⟨73647261335250862539625183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98196348447001150052833577 73647261335250862539625183)
        ·
          refine ⟨110470892002876293809437775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73647261335250862539625183 110470892002876293809437775)
          ·
            refine ⟨165706338004314440714156663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110470892002876293809437775 165706338004314440714156663)
            ·
              refine ⟨248559507006471661071234995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165706338004314440714156663 248559507006471661071234995)
              ·
                refine ⟨372839260509707491606852493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248559507006471661071234995 372839260509707491606852493)
                ·
                  refine ⟨139814722691140309352569685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372839260509707491606852493 139814722691140309352569685)
                  ·
                    refine ⟨819226890768400250112713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 139814722691140309352569685 819226890768400250112713)
                    ·
                      rfl

theorem cell23_4786316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_4786316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786316 prefixEnd_4786316 := by exact prefixLift 4786316
  have htrace : WordTrace (prefixWord ++ tailWord_4786316) baseStart_4786316 baseEnd_4786316 := by
    simpa [prefixWord, tailWord_4786316, baseEnd_4786316] using wordTrace_append hprefix tailTrace_4786316
  have hstable : (prefixWord ++ tailWord_4786316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786316).length < 2 ^ (prefixWord ++ tailWord_4786316).sum := by decide
  have hdescent : baseEnd_4786316 < baseStart_4786316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786373 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_4786373 : Nat := 118140960795 + 4786373 * 2 ^ 59
def prefixEnd_4786373 : Nat := 4983230072969 + 3 ^ 40 * 4786373 * 2
def baseEnd_4786373 : Nat := 2457709940702507027325377

theorem tailTrace_4786373 : CollatzResearch.WordTrace tailWord_4786373 prefixEnd_4786373 2457709940702507027325377 := by
  unfold tailWord_4786373
  simp only [CollatzResearch.WordTrace]
  refine ⟨174573365088795543273195773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116382243392530362182130515 174573365088795543273195773)
  ·
    refine ⟨65465011908298328727448415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174573365088795543273195773 65465011908298328727448415)
    ·
      refine ⟨98197517862447493091172623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65465011908298328727448415 98197517862447493091172623)
      ·
        refine ⟨147296276793671239636758935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98197517862447493091172623 147296276793671239636758935)
        ·
          refine ⟨220944415190506859455138403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147296276793671239636758935 220944415190506859455138403)
          ·
            refine ⟨331416622785760289182707605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220944415190506859455138403 331416622785760289182707605)
            ·
              refine ⟨15535154193082513555439419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 331416622785760289182707605 15535154193082513555439419)
              ·
                refine ⟨23302731289623770333159129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15535154193082513555439419 23302731289623770333159129)
                ·
                  refine ⟨17477048467217827749869347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23302731289623770333159129 17477048467217827749869347)
                  ·
                    refine ⟨26215572700826741624804021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17477048467217827749869347 26215572700826741624804021)
                    ·
                      refine ⟨2457709940702507027325377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26215572700826741624804021 2457709940702507027325377)
                      ·
                        rfl

theorem cell23_4786373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_4786373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786373 prefixEnd_4786373 := by exact prefixLift 4786373
  have htrace : WordTrace (prefixWord ++ tailWord_4786373) baseStart_4786373 baseEnd_4786373 := by
    simpa [prefixWord, tailWord_4786373, baseEnd_4786373] using wordTrace_append hprefix tailTrace_4786373
  have hstable : (prefixWord ++ tailWord_4786373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786373).length < 2 ^ (prefixWord ++ tailWord_4786373).sum := by decide
  have hdescent : baseEnd_4786373 < baseStart_4786373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786383 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_4786383 : Nat := 118140960795 + 4786383 * 2 ^ 59
def prefixEnd_4786383 : Nat := 4983230072969 + 3 ^ 40 * 4786383 * 2
def baseEnd_4786383 : Nat := 2457715075509051988200331

theorem tailTrace_4786383 : CollatzResearch.WordTrace tailWord_4786383 prefixEnd_4786383 2457715075509051988200331 := by
  unfold tailWord_4786383
  simp only [CollatzResearch.WordTrace]
  refine ⟨174573729818759314981059803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116382486545839543320706535 174573729818759314981059803)
  ·
    refine ⟨261860594728138972471589705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174573729818759314981059803 261860594728138972471589705)
    ·
      refine ⟨196395446046104229353692279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261860594728138972471589705 196395446046104229353692279)
      ·
        refine ⟨294593169069156344030538419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196395446046104229353692279 294593169069156344030538419)
        ·
          refine ⟨441889753603734516045807629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294593169069156344030538419 441889753603734516045807629)
          ·
            refine ⟨165708657601400443517177861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 441889753603734516045807629 165708657601400443517177861)
            ·
              refine ⟨31070373300262583159470849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165708657601400443517177861 31070373300262583159470849)
              ·
                refine ⟨23302779975196937369603137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31070373300262583159470849 23302779975196937369603137)
                ·
                  refine ⟨17477084981397703027202353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23302779975196937369603137 17477084981397703027202353)
                  ·
                    refine ⟨13107813736048277270401765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17477084981397703027202353 13107813736048277270401765)
                    ·
                      refine ⟨2457715075509051988200331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13107813736048277270401765 2457715075509051988200331)
                      ·
                        rfl

theorem cell23_4786383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_4786383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786383 prefixEnd_4786383 := by exact prefixLift 4786383
  have htrace : WordTrace (prefixWord ++ tailWord_4786383) baseStart_4786383 baseEnd_4786383 := by
    simpa [prefixWord, tailWord_4786383, baseEnd_4786383] using wordTrace_append hprefix tailTrace_4786383
  have hstable : (prefixWord ++ tailWord_4786383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786383).length < 2 ^ (prefixWord ++ tailWord_4786383).sum := by decide
  have hdescent : baseEnd_4786383 < baseStart_4786383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786478 : List Nat := [4, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_4786478 : Nat := 118140960795 + 4786478 * 2 ^ 59
def prefixEnd_4786478 : Nat := 4983230072969 + 3 ^ 40 * 4786478 * 2
def baseEnd_4786478 : Nat := 273084872907914346279155

theorem tailTrace_4786478 : CollatzResearch.WordTrace tailWord_4786478 prefixEnd_4786478 273084872907914346279155 := by
  unfold tailWord_4786478
  simp only [CollatzResearch.WordTrace]
  refine ⟨21822149344176893275721011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116384796502276764137178725 21822149344176893275721011)
  ·
    refine ⟨32733224016265339913581517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21822149344176893275721011 32733224016265339913581517)
    ·
      refine ⟨12274959006099502467593069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32733224016265339913581517 12274959006099502467593069)
      ·
        refine ⟨4603109627287313425347401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12274959006099502467593069 4603109627287313425347401)
        ·
          refine ⟨3452332220465485069010551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4603109627287313425347401 3452332220465485069010551)
          ·
            refine ⟨5178498330698227603515827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452332220465485069010551 5178498330698227603515827)
            ·
              refine ⟨7767747496047341405273741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5178498330698227603515827 7767747496047341405273741)
              ·
                refine ⟨2912905311017753026977653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7767747496047341405273741 2912905311017753026977653)
                ·
                  refine ⟨273084872907914346279155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2912905311017753026977653 273084872907914346279155)
                  ·
                    rfl

theorem cell23_4786478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_4786478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786478 prefixEnd_4786478 := by exact prefixLift 4786478
  have htrace : WordTrace (prefixWord ++ tailWord_4786478) baseStart_4786478 baseEnd_4786478 := by
    simpa [prefixWord, tailWord_4786478, baseEnd_4786478] using wordTrace_append hprefix tailTrace_4786478
  have hstable : (prefixWord ++ tailWord_4786478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786478).length < 2 ^ (prefixWord ++ tailWord_4786478).sum := by decide
  have hdescent : baseEnd_4786478 < baseStart_4786478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786483 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 10]
def baseStart_4786483 : Nat := 118140960795 + 4786483 * 2 ^ 59
def prefixEnd_4786483 : Nat := 4983230072969 + 3 ^ 40 * 4786483 * 2
def baseEnd_4786483 : Nat := 273085158174944621883319

theorem tailTrace_4786483 : CollatzResearch.WordTrace tailWord_4786483 prefixEnd_4786483 273085158174944621883319 := by
  unfold tailWord_4786483
  simp only [CollatzResearch.WordTrace]
  refine ⟨174577377118397032059700103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116384918078931354706466735 174577377118397032059700103)
  ·
    refine ⟨261866065677595548089550155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174577377118397032059700103 261866065677595548089550155)
    ·
      refine ⟨392799098516393322134325233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261866065677595548089550155 392799098516393322134325233)
      ·
        refine ⟨294599323887294991600743925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392799098516393322134325233 294599323887294991600743925)
        ·
          refine ⟨27618686614433905462569743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 294599323887294991600743925 27618686614433905462569743)
          ·
            refine ⟨41428029921650858193854615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27618686614433905462569743 41428029921650858193854615)
            ·
              refine ⟨62142044882476287290781923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41428029921650858193854615 62142044882476287290781923)
              ·
                refine ⟨93213067323714430936172885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62142044882476287290781923 93213067323714430936172885)
                ·
                  refine ⟨273085158174944621883319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 93213067323714430936172885 273085158174944621883319)
                  ·
                    rfl

theorem cell23_4786483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 10].length) (baseStart_4786483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786483 prefixEnd_4786483 := by exact prefixLift 4786483
  have htrace : WordTrace (prefixWord ++ tailWord_4786483) baseStart_4786483 baseEnd_4786483 := by
    simpa [prefixWord, tailWord_4786483, baseEnd_4786483] using wordTrace_append hprefix tailTrace_4786483
  have hstable : (prefixWord ++ tailWord_4786483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786483).length < 2 ^ (prefixWord ++ tailWord_4786483).sum := by decide
  have hdescent : baseEnd_4786483 < baseStart_4786483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786510 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_4786510 : Nat := 118140960795 + 4786510 * 2 ^ 59
def prefixEnd_4786510 : Nat := 4983230072969 + 3 ^ 40 * 4786510 * 2
def baseEnd_4786510 : Nat := 2457780287552172991312247

theorem tailTrace_4786510 : CollatzResearch.WordTrace tailWord_4786510 prefixEnd_4786510 2457780287552172991312247 := by
  unfold tailWord_4786510
  simp only [CollatzResearch.WordTrace]
  refine ⟨21822295236162401958866623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116385574592866143780621989 21822295236162401958866623)
  ·
    refine ⟨32733442854243602938299935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21822295236162401958866623 32733442854243602938299935)
    ·
      refine ⟨49100164281365404407449903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32733442854243602938299935 49100164281365404407449903)
      ·
        refine ⟨73650246422048106611174855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49100164281365404407449903 73650246422048106611174855)
        ·
          refine ⟨110475369633072159916762283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73650246422048106611174855 110475369633072159916762283)
          ·
            refine ⟨165713054449608239875143425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110475369633072159916762283 165713054449608239875143425)
            ·
              refine ⟨124284790837206179906357569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165713054449608239875143425 124284790837206179906357569)
              ·
                refine ⟨93213593127904634929768177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124284790837206179906357569 93213593127904634929768177)
                ·
                  refine ⟨69910194845928476197326133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93213593127904634929768177 69910194845928476197326133)
                  ·
                    refine ⟨6554080766805794643499325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69910194845928476197326133 6554080766805794643499325)
                    ·
                      refine ⟨2457780287552172991312247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6554080766805794643499325 2457780287552172991312247)
                      ·
                        rfl

theorem cell23_4786510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_4786510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786510 prefixEnd_4786510 := by exact prefixLift 4786510
  have htrace : WordTrace (prefixWord ++ tailWord_4786510) baseStart_4786510 baseEnd_4786510 := by
    simpa [prefixWord, tailWord_4786510, baseEnd_4786510] using wordTrace_append hprefix tailTrace_4786510
  have hstable : (prefixWord ++ tailWord_4786510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786510).length < 2 ^ (prefixWord ++ tailWord_4786510).sum := by decide
  have hdescent : baseEnd_4786510 < baseStart_4786510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786517 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 6]
def baseStart_4786517 : Nat := 118140960795 + 4786517 * 2 ^ 59
def prefixEnd_4786517 : Nat := 4983230072969 + 3 ^ 40 * 4786517 * 2
def baseEnd_4786517 : Nat := 273087097990750495991635

theorem tailTrace_4786517 : CollatzResearch.WordTrace tailWord_4786517 prefixEnd_4786517 273087097990750495991635 := by
  unfold tailWord_4786517
  simp only [CollatzResearch.WordTrace]
  refine ⟨174578617200273855866437805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116385744800182570577625203 174578617200273855866437805)
  ·
    refine ⟨65466981450102695949914177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174578617200273855866437805 65466981450102695949914177)
    ·
      refine ⟨49100236087577021962435633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65466981450102695949914177 49100236087577021962435633)
      ·
        refine ⟨36825177065682766471826725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49100236087577021962435633 36825177065682766471826725)
        ·
          refine ⟨6904720699815518713467511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36825177065682766471826725 6904720699815518713467511)
          ·
            refine ⟨10357081049723278070201267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904720699815518713467511 10357081049723278070201267)
            ·
              refine ⟨15535621574584917105301901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10357081049723278070201267 15535621574584917105301901)
              ·
                refine ⟨5825858090469343914488213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15535621574584917105301901 5825858090469343914488213)
                ·
                  refine ⟨273087097990750495991635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5825858090469343914488213 273087097990750495991635)
                  ·
                    rfl

theorem cell23_4786517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_4786517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786517 prefixEnd_4786517 := by exact prefixLift 4786517
  have htrace : WordTrace (prefixWord ++ tailWord_4786517) baseStart_4786517 baseEnd_4786517 := by
    simpa [prefixWord, tailWord_4786517, baseEnd_4786517] using wordTrace_append hprefix tailTrace_4786517
  have hstable : (prefixWord ++ tailWord_4786517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786517).length < 2 ^ (prefixWord ++ tailWord_4786517).sum := by decide
  have hdescent : baseEnd_4786517 < baseStart_4786517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786527 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 3]
def baseStart_4786527 : Nat := 118140960795 + 4786527 * 2 ^ 59
def prefixEnd_4786527 : Nat := 4983230072969 + 3 ^ 40 * 4786527 * 2
def baseEnd_4786527 : Nat := 2457789016723299424799669

theorem tailTrace_4786527 : CollatzResearch.WordTrace tailWord_4786527 prefixEnd_4786527 2457789016723299424799669 := by
  unfold tailWord_4786527
  simp only [CollatzResearch.WordTrace]
  refine ⟨174578981930237627574301835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116385987953491751716201223 174578981930237627574301835)
  ·
    refine ⟨261868472895356441361452753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174578981930237627574301835 261868472895356441361452753)
    ·
      refine ⟨196401354671517331021089565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261868472895356441361452753 196401354671517331021089565)
      ·
        refine ⟨73650508001818999132908587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196401354671517331021089565 73650508001818999132908587)
        ·
          refine ⟨110475762002728498699362881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73650508001818999132908587 110475762002728498699362881)
          ·
            refine ⟨82856821502046374024522161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110475762002728498699362881 82856821502046374024522161)
            ·
              refine ⟨62142616126534780518391621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82856821502046374024522161 62142616126534780518391621)
              ·
                refine ⟨11651740523725271347198429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62142616126534780518391621 11651740523725271347198429)
                ·
                  refine ⟨4369402696396976755199411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11651740523725271347198429 4369402696396976755199411)
                  ·
                    refine ⟨6554104044595465132799117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369402696396976755199411 6554104044595465132799117)
                    ·
                      refine ⟨2457789016723299424799669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6554104044595465132799117 2457789016723299424799669)
                      ·
                        rfl

theorem cell23_4786527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_4786527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786527 prefixEnd_4786527 := by exact prefixLift 4786527
  have htrace : WordTrace (prefixWord ++ tailWord_4786527) baseStart_4786527 baseEnd_4786527 := by
    simpa [prefixWord, tailWord_4786527, baseEnd_4786527] using wordTrace_append hprefix tailTrace_4786527
  have hstable : (prefixWord ++ tailWord_4786527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786527).length < 2 ^ (prefixWord ++ tailWord_4786527).sum := by decide
  have hdescent : baseEnd_4786527 < baseStart_4786527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786582 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4786582 : Nat := 118140960795 + 4786582 * 2 ^ 59
def prefixEnd_4786582 : Nat := 4983230072969 + 3 ^ 40 * 4786582 * 2
def baseEnd_4786582 : Nat := 2457817258159296709611917

theorem tailTrace_4786582 : CollatzResearch.WordTrace tailWord_4786582 prefixEnd_4786582 2457817258159296709611917 := by
  unfold tailWord_4786582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10911311746564898247972125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116387325296692247978369333 10911311746564898247972125)
  ·
    refine ⟨4091741904961836842989547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10911311746564898247972125 4091741904961836842989547)
    ·
      refine ⟨6137612857442755264484321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4091741904961836842989547 6137612857442755264484321)
      ·
        refine ⟨4603209643082066448363241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6137612857442755264484321 4603209643082066448363241)
        ·
          refine ⟨3452407232311549836272431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4603209643082066448363241 3452407232311549836272431)
          ·
            refine ⟨5178610848467324754408647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452407232311549836272431 5178610848467324754408647)
            ·
              refine ⟨7767916272700987131612971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5178610848467324754408647 7767916272700987131612971)
              ·
                refine ⟨11651874409051480697419457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7767916272700987131612971 11651874409051480697419457)
                ·
                  refine ⟨8738905806788610523064593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11651874409051480697419457 8738905806788610523064593)
                  ·
                    refine ⟨6554179355091457892298445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8738905806788610523064593 6554179355091457892298445)
                    ·
                      refine ⟨2457817258159296709611917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6554179355091457892298445 2457817258159296709611917)
                      ·
                        rfl

theorem cell23_4786582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4786582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786582 prefixEnd_4786582 := by exact prefixLift 4786582
  have htrace : WordTrace (prefixWord ++ tailWord_4786582) baseStart_4786582 baseEnd_4786582 := by
    simpa [prefixWord, tailWord_4786582, baseEnd_4786582] using wordTrace_append hprefix tailTrace_4786582
  have hstable : (prefixWord ++ tailWord_4786582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786582).length < 2 ^ (prefixWord ++ tailWord_4786582).sum := by decide
  have hdescent : baseEnd_4786582 < baseStart_4786582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786628 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_4786628 : Nat := 118140960795 + 4786628 * 2 ^ 59
def prefixEnd_4786628 : Nat := 4983230072969 + 3 ^ 40 * 4786628 * 2
def baseEnd_4786628 : Nat := 819280292756467843212235

theorem tailTrace_4786628 : CollatzResearch.WordTrace tailWord_4786628 prefixEnd_4786628 819280292756467843212235 := by
  unfold tailWord_4786628
  simp only [CollatzResearch.WordTrace]
  refine ⟨87291332851435860911864269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116388443801914481215819025 87291332851435860911864269)
  ·
    refine ⟨32734249819288447841949101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87291332851435860911864269 32734249819288447841949101)
    ·
      refine ⟨12275343682233167940730913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32734249819288447841949101 12275343682233167940730913)
      ·
        refine ⟨9206507761674875955548185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12275343682233167940730913 9206507761674875955548185)
        ·
          refine ⟨6904880821256156966661139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9206507761674875955548185 6904880821256156966661139)
          ·
            refine ⟨10357321231884235449991709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904880821256156966661139 10357321231884235449991709)
            ·
              refine ⟨3883995461956588293746891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10357321231884235449991709 3883995461956588293746891)
              ·
                refine ⟨5825993192934882440620337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3883995461956588293746891 5825993192934882440620337)
                ·
                  refine ⟨4369494894701161830465253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5825993192934882440620337 4369494894701161830465253)
                  ·
                    refine ⟨819280292756467843212235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369494894701161830465253 819280292756467843212235)
                    ·
                      rfl

theorem cell23_4786628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_4786628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786628 prefixEnd_4786628 := by exact prefixLift 4786628
  have htrace : WordTrace (prefixWord ++ tailWord_4786628) baseStart_4786628 baseEnd_4786628 := by
    simpa [prefixWord, tailWord_4786628, baseEnd_4786628] using wordTrace_append hprefix tailTrace_4786628
  have hstable : (prefixWord ++ tailWord_4786628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786628).length < 2 ^ (prefixWord ++ tailWord_4786628).sum := by decide
  have hdescent : baseEnd_4786628 < baseStart_4786628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786691 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 2, 2, 2]
def baseStart_4786691 : Nat := 118140960795 + 4786691 * 2 ^ 59
def prefixEnd_4786691 : Nat := 4983230072969 + 3 ^ 40 * 4786691 * 2
def baseEnd_4786691 : Nat := 2457873227550636783148915

theorem tailTrace_4786691 : CollatzResearch.WordTrace tailWord_4786691 prefixEnd_4786691 2457873227550636783148915 := by
  unfold tailWord_4786691
  simp only [CollatzResearch.WordTrace]
  refine ⟨174584963501643483583271927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116389975667762322388847951 174584963501643483583271927)
  ·
    refine ⟨261877445252465225374907891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174584963501643483583271927 261877445252465225374907891)
    ·
      refine ⟨392816167878697838062361837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261877445252465225374907891 392816167878697838062361837)
      ·
        refine ⟨147306062954511689273385689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392816167878697838062361837 147306062954511689273385689)
        ·
          refine ⟨110479547215883766955039267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147306062954511689273385689 110479547215883766955039267)
          ·
            refine ⟨165719320823825650432558901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110479547215883766955039267 165719320823825650432558901)
            ·
              refine ⟨15536186327233654728052397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165719320823825650432558901 15536186327233654728052397)
              ·
                refine ⟨5826069872712620523019649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15536186327233654728052397 5826069872712620523019649)
                ·
                  refine ⟨4369552404534465392264737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5826069872712620523019649 4369552404534465392264737)
                  ·
                    refine ⟨3277164303400849044198553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4369552404534465392264737 3277164303400849044198553)
                    ·
                      refine ⟨2457873227550636783148915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277164303400849044198553 2457873227550636783148915)
                      ·
                        rfl

theorem cell23_4786691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_4786691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786691 prefixEnd_4786691 := by exact prefixLift 4786691
  have htrace : WordTrace (prefixWord ++ tailWord_4786691) baseStart_4786691 baseEnd_4786691 := by
    simpa [prefixWord, tailWord_4786691, baseEnd_4786691] using wordTrace_append hprefix tailTrace_4786691
  have hstable : (prefixWord ++ tailWord_4786691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786691).length < 2 ^ (prefixWord ++ tailWord_4786691).sum := by decide
  have hdescent : baseEnd_4786691 < baseStart_4786691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786695 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_4786695 : Nat := 118140960795 + 4786695 * 2 ^ 59
def prefixEnd_4786695 : Nat := 4983230072969 + 3 ^ 40 * 4786695 * 2
def baseEnd_4786695 : Nat := 2457875281473254767498897

theorem tailTrace_4786695 : CollatzResearch.WordTrace tailWord_4786695 prefixEnd_4786695 2457875281473254767498897 := by
  unfold tailWord_4786695
  simp only [CollatzResearch.WordTrace]
  refine ⟨174585109393628992266417539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116390072929085994844278359 174585109393628992266417539)
  ·
    refine ⟨261877664090443488399626309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174585109393628992266417539 261877664090443488399626309)
    ·
      refine ⟨49102062016958154074929933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261877664090443488399626309 49102062016958154074929933)
      ·
        refine ⟨18413273256359307778098725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49102062016958154074929933 18413273256359307778098725)
        ·
          refine ⟨3452488735567370208393511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18413273256359307778098725 3452488735567370208393511)
          ·
            refine ⟨5178733103351055312590267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452488735567370208393511 5178733103351055312590267)
            ·
              refine ⟨7768099655026582968885401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5178733103351055312590267 7768099655026582968885401)
              ·
                refine ⟨5826074741269937226664051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7768099655026582968885401 5826074741269937226664051)
                ·
                  refine ⟨8739112111904905839996077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826074741269937226664051 8739112111904905839996077)
                  ·
                    refine ⟨3277167041964339689998529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8739112111904905839996077 3277167041964339689998529)
                    ·
                      refine ⟨2457875281473254767498897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277167041964339689998529 2457875281473254767498897)
                      ·
                        rfl

theorem cell23_4786695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_4786695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786695 prefixEnd_4786695 := by exact prefixLift 4786695
  have htrace : WordTrace (prefixWord ++ tailWord_4786695) baseStart_4786695 baseEnd_4786695 := by
    simpa [prefixWord, tailWord_4786695, baseEnd_4786695] using wordTrace_append hprefix tailTrace_4786695
  have hstable : (prefixWord ++ tailWord_4786695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786695).length < 2 ^ (prefixWord ++ tailWord_4786695).sum := by decide
  have hdescent : baseEnd_4786695 < baseStart_4786695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786708 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_4786708 : Nat := 118140960795 + 4786708 * 2 ^ 59
def prefixEnd_4786708 : Nat := 4983230072969 + 3 ^ 40 * 4786708 * 2
def baseEnd_4786708 : Nat := 2457881956721763216636337

theorem tailTrace_4786708 : CollatzResearch.WordTrace tailWord_4786708 prefixEnd_4786708 2457881956721763216636337 := by
  unfold tailWord_4786708
  simp only [CollatzResearch.WordTrace]
  refine ⟨87292791771290947743320389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116390389028387930324427185 87292791771290947743320389)
  ·
    refine ⟨16367398457117052701872573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87292791771290947743320389 16367398457117052701872573)
    ·
      refine ⟨6137774421418894763202215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16367398457117052701872573 6137774421418894763202215)
      ·
        refine ⟨9206661632128342144803323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6137774421418894763202215 9206661632128342144803323)
        ·
          refine ⟨13809992448192513217204985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9206661632128342144803323 13809992448192513217204985)
          ·
            refine ⟨10357494336144384912903739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13809992448192513217204985 10357494336144384912903739)
            ·
              refine ⟨15536241504216577369355609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10357494336144384912903739 15536241504216577369355609)
              ·
                refine ⟨11652181128162433027016707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15536241504216577369355609 11652181128162433027016707)
                ·
                  refine ⟨17478271692243649540525061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11652181128162433027016707 17478271692243649540525061)
                  ·
                    refine ⟨3277175942295684288848449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17478271692243649540525061 3277175942295684288848449)
                    ·
                      refine ⟨2457881956721763216636337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277175942295684288848449 2457881956721763216636337)
                      ·
                        rfl

theorem cell23_4786708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_4786708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786708 prefixEnd_4786708 := by exact prefixLift 4786708
  have htrace : WordTrace (prefixWord ++ tailWord_4786708) baseStart_4786708 baseEnd_4786708 := by
    simpa [prefixWord, tailWord_4786708, baseEnd_4786708] using wordTrace_append hprefix tailTrace_4786708
  have hstable : (prefixWord ++ tailWord_4786708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786708).length < 2 ^ (prefixWord ++ tailWord_4786708).sum := by decide
  have hdescent : baseEnd_4786708 < baseStart_4786708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786737 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_4786737 : Nat := 118140960795 + 4786737 * 2 ^ 59
def prefixEnd_4786737 : Nat := 4983230072969 + 3 ^ 40 * 4786737 * 2
def baseEnd_4786737 : Nat := 2457896847660743603173703

theorem tailTrace_4786737 : CollatzResearch.WordTrace tailWord_4786737 prefixEnd_4786737 2457896847660743603173703 := by
  unfold tailWord_4786737
  simp only [CollatzResearch.WordTrace]
  refine ⟨174586641259476833439446465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116391094172984555626297643 174586641259476833439446465)
  ·
    refine ⟨130939980944607625079584849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174586641259476833439446465 130939980944607625079584849)
    ·
      refine ⟨98204985708455718809688637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130939980944607625079584849 98204985708455718809688637)
      ·
        refine ⟨36826869640670894553633239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98204985708455718809688637 36826869640670894553633239)
        ·
          refine ⟨55240304461006341830449859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36826869640670894553633239 55240304461006341830449859)
          ·
            refine ⟨82860456691509512745674789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55240304461006341830449859 82860456691509512745674789)
            ·
              refine ⟨15536335629658033639814023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82860456691509512745674789 15536335629658033639814023)
              ·
                refine ⟨23304503444487050459721035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15536335629658033639814023 23304503444487050459721035)
                ·
                  refine ⟨34956755166730575689581553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23304503444487050459721035 34956755166730575689581553)
                  ·
                    refine ⟨26217566375047931767186165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34956755166730575689581553 26217566375047931767186165)
                    ·
                      refine ⟨2457896847660743603173703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26217566375047931767186165 2457896847660743603173703)
                      ·
                        rfl

theorem cell23_4786737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_4786737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786737 prefixEnd_4786737 := by exact prefixLift 4786737
  have htrace : WordTrace (prefixWord ++ tailWord_4786737) baseStart_4786737 baseEnd_4786737 := by
    simpa [prefixWord, tailWord_4786737, baseEnd_4786737] using wordTrace_append hprefix tailTrace_4786737
  have hstable : (prefixWord ++ tailWord_4786737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786737).length < 2 ^ (prefixWord ++ tailWord_4786737).sum := by decide
  have hdescent : baseEnd_4786737 < baseStart_4786737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786764 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 1, 6, 2]
def baseStart_4786764 : Nat := 118140960795 + 4786764 * 2 ^ 59
def prefixEnd_4786764 : Nat := 4983230072969 + 3 ^ 40 * 4786764 * 2
def baseEnd_4786764 : Nat := 2457910711638414997536079

theorem tailTrace_4786764 : CollatzResearch.WordTrace tailWord_4786764 prefixEnd_4786764 2457910711638414997536079 := by
  unfold tailWord_4786764
  simp only [CollatzResearch.WordTrace]
  refine ⟨87293813015189508525339673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116391750686919344700452897 87293813015189508525339673)
  ·
    refine ⟨65470359761392131394004755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87293813015189508525339673 65470359761392131394004755)
    ·
      refine ⟨98205539642088197091007133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65470359761392131394004755 98205539642088197091007133)
      ·
        refine ⟨36827077365783073909127675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98205539642088197091007133 36827077365783073909127675)
        ·
          refine ⟨55240616048674610863691513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36827077365783073909127675 55240616048674610863691513)
          ·
            refine ⟨41430462036505958147768635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55240616048674610863691513 41430462036505958147768635)
            ·
              refine ⟨62145693054758937221652953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41430462036505958147768635 62145693054758937221652953)
              ·
                refine ⟨46609269791069202916239715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62145693054758937221652953 46609269791069202916239715)
                ·
                  refine ⟨69913904686603804374359573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46609269791069202916239715 69913904686603804374359573)
                  ·
                    refine ⟨3277214282184553330048105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69913904686603804374359573 3277214282184553330048105)
                    ·
                      refine ⟨2457910711638414997536079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277214282184553330048105 2457910711638414997536079)
                      ·
                        rfl

theorem cell23_4786764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_4786764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786764 prefixEnd_4786764 := by exact prefixLift 4786764
  have htrace : WordTrace (prefixWord ++ tailWord_4786764) baseStart_4786764 baseEnd_4786764 := by
    simpa [prefixWord, tailWord_4786764, baseEnd_4786764] using wordTrace_append hprefix tailTrace_4786764
  have hstable : (prefixWord ++ tailWord_4786764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786764).length < 2 ^ (prefixWord ++ tailWord_4786764).sum := by decide
  have hdescent : baseEnd_4786764 < baseStart_4786764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786784 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3]
def baseStart_4786784 : Nat := 118140960795 + 4786784 * 2 ^ 59
def prefixEnd_4786784 : Nat := 4983230072969 + 3 ^ 40 * 4786784 * 2
def baseEnd_4786784 : Nat := 2457920981251504919285987

theorem tailTrace_4786784 : CollatzResearch.WordTrace tailWord_4786784 prefixEnd_4786784 2457920981251504919285987 := by
  unfold tailWord_4786784
  simp only [CollatzResearch.WordTrace]
  refine ⟨87294177745153280233203703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116392236993537706977604937 87294177745153280233203703)
  ·
    refine ⟨130941266617729920349805555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87294177745153280233203703 130941266617729920349805555)
    ·
      refine ⟨196411899926594880524708333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130941266617729920349805555 196411899926594880524708333)
      ·
        refine ⟨73654462472473080196765625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196411899926594880524708333 73654462472473080196765625)
        ·
          refine ⟨55240846854354810147574219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73654462472473080196765625 55240846854354810147574219)
          ·
            refine ⟨82861270281532215221361329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55240846854354810147574219 82861270281532215221361329)
            ·
              refine ⟨62145952711149161416020997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82861270281532215221361329 62145952711149161416020997)
              ·
                refine ⟨11652366133340467765503937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62145952711149161416020997 11652366133340467765503937)
                ·
                  refine ⟨8739274600005350824127953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11652366133340467765503937 8739274600005350824127953)
                  ·
                    refine ⟨6554455950004013118095965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8739274600005350824127953 6554455950004013118095965)
                    ·
                      refine ⟨2457920981251504919285987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6554455950004013118095965 2457920981251504919285987)
                      ·
                        rfl

theorem cell23_4786784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_4786784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786784 prefixEnd_4786784 := by exact prefixLift 4786784
  have htrace : WordTrace (prefixWord ++ tailWord_4786784) baseStart_4786784 baseEnd_4786784 := by
    simpa [prefixWord, tailWord_4786784, baseEnd_4786784] using wordTrace_append hprefix tailTrace_4786784
  have hstable : (prefixWord ++ tailWord_4786784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786784).length < 2 ^ (prefixWord ++ tailWord_4786784).sum := by decide
  have hdescent : baseEnd_4786784 < baseStart_4786784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786787 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 8]
def baseStart_4786787 : Nat := 118140960795 + 4786787 * 2 ^ 59
def prefixEnd_4786787 : Nat := 4983230072969 + 3 ^ 40 * 4786787 * 2
def baseEnd_4786787 : Nat := 273102502410385378616497

theorem tailTrace_4786787 : CollatzResearch.WordTrace tailWord_4786787 prefixEnd_4786787 273102502410385378616497 := by
  unfold tailWord_4786787
  simp only [CollatzResearch.WordTrace]
  refine ⟨174588464909295691978766615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116392309939530461319177743 174588464909295691978766615)
  ·
    refine ⟨261882697363943537968149923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174588464909295691978766615 261882697363943537968149923)
    ·
      refine ⟨392824046045915306952224885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261882697363943537968149923 392824046045915306952224885)
      ·
        refine ⟨36827254316804560026771083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 392824046045915306952224885 36827254316804560026771083)
        ·
          refine ⟨55240881475206840040156625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36827254316804560026771083 55240881475206840040156625)
          ·
            refine ⟨41430661106405130030117469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55240881475206840040156625 41430661106405130030117469)
            ·
              refine ⟨15536497914901923761294051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41430661106405130030117469 15536497914901923761294051)
              ·
                refine ⟨23304746872352885641941077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15536497914901923761294051 23304746872352885641941077)
                ·
                  refine ⟨273102502410385378616497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23304746872352885641941077 273102502410385378616497)
                  ·
                    rfl

theorem cell23_4786787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 8].length) (baseStart_4786787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786787 prefixEnd_4786787 := by exact prefixLift 4786787
  have htrace : WordTrace (prefixWord ++ tailWord_4786787) baseStart_4786787 baseEnd_4786787 := by
    simpa [prefixWord, tailWord_4786787, baseEnd_4786787] using wordTrace_append hprefix tailTrace_4786787
  have hstable : (prefixWord ++ tailWord_4786787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786787).length < 2 ^ (prefixWord ++ tailWord_4786787).sum := by decide
  have hdescent : baseEnd_4786787 < baseStart_4786787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786841 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 2, 3, 2]
def baseStart_4786841 : Nat := 118140960795 + 4786841 * 2 ^ 59
def prefixEnd_4786841 : Nat := 4983230072969 + 3 ^ 40 * 4786841 * 2
def baseEnd_4786841 : Nat := 2457950249648811196273225

theorem tailTrace_4786841 : CollatzResearch.WordTrace tailWord_4786841 prefixEnd_4786841 2457950249648811196273225 := by
  unfold tailWord_4786841
  simp only [CollatzResearch.WordTrace]
  refine ⟨174590434451100059201232377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116393622967400039467488251 174590434451100059201232377)
  ·
    refine ⟨130942825838325044400924283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174590434451100059201232377 130942825838325044400924283)
    ·
      refine ⟨196414238757487566601386425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130942825838325044400924283 196414238757487566601386425)
      ·
        refine ⟨147310679068115674951039819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196414238757487566601386425 147310679068115674951039819)
        ·
          refine ⟨220966018602173512426559729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147310679068115674951039819 220966018602173512426559729)
          ·
            refine ⟨165724513951630134319919797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220966018602173512426559729 165724513951630134319919797)
            ·
              refine ⟨15536673182965325092492481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165724513951630134319919797 15536673182965325092492481)
              ·
                refine ⟨11652504887223993819369361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15536673182965325092492481 11652504887223993819369361)
                ·
                  refine ⟨8739378665417995364527021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11652504887223993819369361 8739378665417995364527021)
                  ·
                    refine ⟨3277266999531748261697633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8739378665417995364527021 3277266999531748261697633)
                    ·
                      refine ⟨2457950249648811196273225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277266999531748261697633 2457950249648811196273225)
                      ·
                        rfl

theorem cell23_4786841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_4786841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786841 prefixEnd_4786841 := by exact prefixLift 4786841
  have htrace : WordTrace (prefixWord ++ tailWord_4786841) baseStart_4786841 baseEnd_4786841 := by
    simpa [prefixWord, tailWord_4786841, baseEnd_4786841] using wordTrace_append hprefix tailTrace_4786841
  have hstable : (prefixWord ++ tailWord_4786841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786841).length < 2 ^ (prefixWord ++ tailWord_4786841).sum := by decide
  have hdescent : baseEnd_4786841 < baseStart_4786841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786842 : List Nat := [3, 1, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_4786842 : Nat := 118140960795 + 4786842 * 2 ^ 59
def prefixEnd_4786842 : Nat := 4983230072969 + 3 ^ 40 * 4786842 * 2
def baseEnd_4786842 : Nat := 819316921043155230786907

theorem tailTrace_4786842 : CollatzResearch.WordTrace tailWord_4786842 prefixEnd_4786842 819316921043155230786907 := by
  unfold tailWord_4786842
  simp only [CollatzResearch.WordTrace]
  refine ⟨43647617731024109093004695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116393647282730957581345853 43647617731024109093004695)
  ·
    refine ⟨65471426596536163639507043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43647617731024109093004695 65471426596536163639507043)
    ·
      refine ⟨98207139894804245459260565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65471426596536163639507043 98207139894804245459260565)
      ·
        refine ⟨4603459682568949005902839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98207139894804245459260565 4603459682568949005902839)
        ·
          refine ⟨6905189523853423508854259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4603459682568949005902839 6905189523853423508854259)
          ·
            refine ⟨10357784285780135263281389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6905189523853423508854259 10357784285780135263281389)
            ·
              refine ⟨3884169107167550723730521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10357784285780135263281389 3884169107167550723730521)
              ·
                refine ⟨2913126830375663042797891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884169107167550723730521 2913126830375663042797891)
                ·
                  refine ⟨4369690245563494564196837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2913126830375663042797891 4369690245563494564196837)
                  ·
                    refine ⟨819316921043155230786907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4369690245563494564196837 819316921043155230786907)
                    ·
                      rfl

theorem cell23_4786842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_4786842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786842 prefixEnd_4786842 := by exact prefixLift 4786842
  have htrace : WordTrace (prefixWord ++ tailWord_4786842) baseStart_4786842 baseEnd_4786842 := by
    simpa [prefixWord, tailWord_4786842, baseEnd_4786842] using wordTrace_append hprefix tailTrace_4786842
  have hstable : (prefixWord ++ tailWord_4786842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786842).length < 2 ^ (prefixWord ++ tailWord_4786842).sum := by decide
  have hdescent : baseEnd_4786842 < baseStart_4786842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786855 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 6]
def baseStart_4786855 : Nat := 118140960795 + 4786855 * 2 ^ 59
def prefixEnd_4786855 : Nat := 4983230072969 + 3 ^ 40 * 4786855 * 2
def baseEnd_4786855 : Nat := 273106382041997126833129

theorem tailTrace_4786855 : CollatzResearch.WordTrace tailWord_4786855 prefixEnd_4786855 273106382041997126833129 := by
  unfold tailWord_4786855
  simp only [CollatzResearch.WordTrace]
  refine ⟨174590945073049339592242019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116393963382032893061494679 174590945073049339592242019)
  ·
    refine ⟨261886417609574009388363029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174590945073049339592242019 261886417609574009388363029)
    ·
      refine ⟨12275925825448781690079517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 261886417609574009388363029 12275925825448781690079517)
      ·
        refine ⟨4603472184543293133779819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12275925825448781690079517 4603472184543293133779819)
        ·
          refine ⟨6905208276814939700669729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4603472184543293133779819 6905208276814939700669729)
          ·
            refine ⟨5178906207611204775502297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6905208276814939700669729 5178906207611204775502297)
            ·
              refine ⟨3884179655708403581626723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5178906207611204775502297 3884179655708403581626723)
              ·
                refine ⟨5826269483562605372440085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884179655708403581626723 5826269483562605372440085)
                ·
                  refine ⟨273106382041997126833129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5826269483562605372440085 273106382041997126833129)
                  ·
                    rfl

theorem cell23_4786855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 6].length) (baseStart_4786855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786855 prefixEnd_4786855 := by exact prefixLift 4786855
  have htrace : WordTrace (prefixWord ++ tailWord_4786855) baseStart_4786855 baseEnd_4786855 := by
    simpa [prefixWord, tailWord_4786855, baseEnd_4786855] using wordTrace_append hprefix tailTrace_4786855
  have hstable : (prefixWord ++ tailWord_4786855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786855).length < 2 ^ (prefixWord ++ tailWord_4786855).sum := by decide
  have hdescent : baseEnd_4786855 < baseStart_4786855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786871 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_4786871 : Nat := 118140960795 + 4786871 * 2 ^ 59
def prefixEnd_4786871 : Nat := 4983230072969 + 3 ^ 40 * 4786871 * 2
def baseEnd_4786871 : Nat := 2457965654068446078898087

theorem tailTrace_4786871 : CollatzResearch.WordTrace tailWord_4786871 prefixEnd_4786871 2457965654068446078898087 := by
  unfold tailWord_4786871
  simp only [CollatzResearch.WordTrace]
  refine ⟨174591528640991374324824467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116394352427327582883216311 174591528640991374324824467)
  ·
    refine ⟨261887292961487061487236701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174591528640991374324824467 261887292961487061487236701)
    ·
      refine ⟨98207734860557648057713763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261887292961487061487236701 98207734860557648057713763)
      ·
        refine ⟨147311602290836472086570645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98207734860557648057713763 147311602290836472086570645)
        ·
          refine ⟨6905231357382959629057999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 147311602290836472086570645 6905231357382959629057999)
          ·
            refine ⟨10357847036074439443586999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6905231357382959629057999 10357847036074439443586999)
            ·
              refine ⟨15536770554111659165380499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10357847036074439443586999 15536770554111659165380499)
              ·
                refine ⟨23305155831167488748070749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15536770554111659165380499 23305155831167488748070749)
                ·
                  refine ⟨8739433436687808280526531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23305155831167488748070749 8739433436687808280526531)
                  ·
                    refine ⟨13109150155031712420789797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8739433436687808280526531 13109150155031712420789797)
                    ·
                      refine ⟨2457965654068446078898087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13109150155031712420789797 2457965654068446078898087)
                      ·
                        rfl

theorem cell23_4786871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_4786871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786871 prefixEnd_4786871 := by exact prefixLift 4786871
  have htrace : WordTrace (prefixWord ++ tailWord_4786871) baseStart_4786871 baseEnd_4786871 := by
    simpa [prefixWord, tailWord_4786871, baseEnd_4786871] using wordTrace_append hprefix tailTrace_4786871
  have hstable : (prefixWord ++ tailWord_4786871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786871).length < 2 ^ (prefixWord ++ tailWord_4786871).sum := by decide
  have hdescent : baseEnd_4786871 < baseStart_4786871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786888 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_4786888 : Nat := 118140960795 + 4786888 * 2 ^ 59
def prefixEnd_4786888 : Nat := 4983230072969 + 3 ^ 40 * 4786888 * 2
def baseEnd_4786888 : Nat := 2457974383239572512385509

theorem tailTrace_4786888 : CollatzResearch.WordTrace tailWord_4786888 prefixEnd_4786888 2457974383239572512385509 := by
  unfold tailWord_4786888
  simp only [CollatzResearch.WordTrace]
  refine ⟨87296074340964893114096659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116394765787953190818795545 87296074340964893114096659)
  ·
    refine ⟨130944111511447339671144989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87296074340964893114096659 130944111511447339671144989)
    ·
      refine ⟨49104041816792752376679371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130944111511447339671144989 49104041816792752376679371)
      ·
        refine ⟨73656062725189128565019057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49104041816792752376679371 73656062725189128565019057)
        ·
          refine ⟨55242047043891846423764293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73656062725189128565019057 55242047043891846423764293)
          ·
            refine ⟨10357883820729721204455805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55242047043891846423764293 10357883820729721204455805)
            ·
              refine ⟨3884206432773645451670927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10357883820729721204455805 3884206432773645451670927)
              ·
                refine ⟨5826309649160468177506391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884206432773645451670927 5826309649160468177506391)
                ·
                  refine ⟨8739464473740702266259587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826309649160468177506391 8739464473740702266259587)
                  ·
                    refine ⟨13109196710611053399389381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8739464473740702266259587 13109196710611053399389381)
                    ·
                      refine ⟨2457974383239572512385509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13109196710611053399389381 2457974383239572512385509)
                      ·
                        rfl

theorem cell23_4786888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_4786888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786888 prefixEnd_4786888 := by exact prefixLift 4786888
  have htrace : WordTrace (prefixWord ++ tailWord_4786888) baseStart_4786888 baseEnd_4786888 := by
    simpa [prefixWord, tailWord_4786888, baseEnd_4786888] using wordTrace_append hprefix tailTrace_4786888
  have hstable : (prefixWord ++ tailWord_4786888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786888).length < 2 ^ (prefixWord ++ tailWord_4786888).sum := by decide
  have hdescent : baseEnd_4786888 < baseStart_4786888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786905 : List Nat := [1, 2, 1, 2, 3, 2, 3, 4, 1, 2, 2]
def baseStart_4786905 : Nat := 118140960795 + 4786905 * 2 ^ 59
def prefixEnd_4786905 : Nat := 4983230072969 + 3 ^ 40 * 4786905 * 2
def baseEnd_4786905 : Nat := 2457983112410698945872931

theorem tailTrace_4786905 : CollatzResearch.WordTrace tailWord_4786905 prefixEnd_4786905 2457983112410698945872931 := by
  unfold tailWord_4786905
  simp only [CollatzResearch.WordTrace]
  refine ⟨174592768722868198131562169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116395179148578798754374779 174592768722868198131562169)
  ·
    refine ⟨130944576542151148598671627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174592768722868198131562169 130944576542151148598671627)
    ·
      refine ⟨196416864813226722898007441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130944576542151148598671627 196416864813226722898007441)
      ·
        refine ⟨147312648609920042173505581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196416864813226722898007441 147312648609920042173505581)
        ·
          refine ⟨55242243228720015815064593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147312648609920042173505581 55242243228720015815064593)
          ·
            refine ⟨41431682421540011861298445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55242243228720015815064593 41431682421540011861298445)
            ·
              refine ⟨15536880908077504447986917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41431682421540011861298445 15536880908077504447986917)
              ·
                refine ⟨2913165170264532083997547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15536880908077504447986917 2913165170264532083997547)
                ·
                  refine ⟨4369747755396798125996321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2913165170264532083997547 4369747755396798125996321)
                  ·
                    refine ⟨3277310816547598594497241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4369747755396798125996321 3277310816547598594497241)
                    ·
                      refine ⟨2457983112410698945872931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277310816547598594497241 2457983112410698945872931)
                      ·
                        rfl

theorem cell23_4786905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_4786905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786905 prefixEnd_4786905 := by exact prefixLift 4786905
  have htrace : WordTrace (prefixWord ++ tailWord_4786905) baseStart_4786905 baseEnd_4786905 := by
    simpa [prefixWord, tailWord_4786905, baseEnd_4786905] using wordTrace_append hprefix tailTrace_4786905
  have hstable : (prefixWord ++ tailWord_4786905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786905).length < 2 ^ (prefixWord ++ tailWord_4786905).sum := by decide
  have hdescent : baseEnd_4786905 < baseStart_4786905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786908 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4786908 : Nat := 118140960795 + 4786908 * 2 ^ 59
def prefixEnd_4786908 : Nat := 4983230072969 + 3 ^ 40 * 4786908 * 2
def baseEnd_4786908 : Nat := 2457984652852662434135417

theorem tailTrace_4786908 : CollatzResearch.WordTrace tailWord_4786908 prefixEnd_4786908 2457984652852662434135417 := by
  unfold tailWord_4786908
  simp only [CollatzResearch.WordTrace]
  refine ⟨87296439070928664821960689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116395252094571553095947585 87296439070928664821960689)
  ·
    refine ⟨65472329303196498616470517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87296439070928664821960689 65472329303196498616470517)
    ·
      refine ⟨6138030872174671745294111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65472329303196498616470517 6138030872174671745294111)
      ·
        refine ⟨9207046308262007617941167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6138030872174671745294111 9207046308262007617941167)
        ·
          refine ⟨13810569462393011426911751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9207046308262007617941167 13810569462393011426911751)
          ·
            refine ⟨20715854193589517140367627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13810569462393011426911751 20715854193589517140367627)
            ·
              refine ⟨31073781290384275710551441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20715854193589517140367627 31073781290384275710551441)
              ·
                refine ⟨23305335967788206782913581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31073781290384275710551441 23305335967788206782913581)
                ·
                  refine ⟨8739500987920577543592593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23305335967788206782913581 8739500987920577543592593)
                  ·
                    refine ⟨6554625740940433157694445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8739500987920577543592593 6554625740940433157694445)
                    ·
                      refine ⟨2457984652852662434135417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6554625740940433157694445 2457984652852662434135417)
                      ·
                        rfl

theorem cell23_4786908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4786908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786908 prefixEnd_4786908 := by exact prefixLift 4786908
  have htrace : WordTrace (prefixWord ++ tailWord_4786908) baseStart_4786908 baseEnd_4786908 := by
    simpa [prefixWord, tailWord_4786908, baseEnd_4786908] using wordTrace_append hprefix tailTrace_4786908
  have hstable : (prefixWord ++ tailWord_4786908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786908).length < 2 ^ (prefixWord ++ tailWord_4786908).sum := by decide
  have hdescent : baseEnd_4786908 < baseStart_4786908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786942 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4786942 : Nat := 118140960795 + 4786942 * 2 ^ 59
def prefixEnd_4786942 : Nat := 4983230072969 + 3 ^ 40 * 4786942 * 2
def baseEnd_4786942 : Nat := 2458002111194915301110261

theorem tailTrace_4786942 : CollatzResearch.WordTrace tailWord_4786942 prefixEnd_4786942 2458002111194915301110261 := by
  unfold tailWord_4786942
  simp only [CollatzResearch.WordTrace]
  refine ⟨21824264777966769181332385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116396078815822768967106053 21824264777966769181332385)
  ·
    refine ⟨16368198583475076885999289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21824264777966769181332385 16368198583475076885999289)
    ·
      refine ⟨12276148937606307664499467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16368198583475076885999289 12276148937606307664499467)
      ·
        refine ⟨18414223406409461496749201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12276148937606307664499467 18414223406409461496749201)
        ·
          refine ⟨13810667554807096122561901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18414223406409461496749201 13810667554807096122561901)
          ·
            refine ⟨5179000333052661045960713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13810667554807096122561901 5179000333052661045960713)
            ·
              refine ⟨3884250249789495784470535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5179000333052661045960713 3884250249789495784470535)
              ·
                refine ⟨5826375374684243676705803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884250249789495784470535 5826375374684243676705803)
                ·
                  refine ⟨8739563062026365515058705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826375374684243676705803 8739563062026365515058705)
                  ·
                    refine ⟨6554672296519774136294029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8739563062026365515058705 6554672296519774136294029)
                    ·
                      refine ⟨2458002111194915301110261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6554672296519774136294029 2458002111194915301110261)
                      ·
                        rfl

theorem cell23_4786942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4786942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786942 prefixEnd_4786942 := by exact prefixLift 4786942
  have htrace : WordTrace (prefixWord ++ tailWord_4786942) baseStart_4786942 baseEnd_4786942 := by
    simpa [prefixWord, tailWord_4786942, baseEnd_4786942] using wordTrace_append hprefix tailTrace_4786942
  have hstable : (prefixWord ++ tailWord_4786942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786942).length < 2 ^ (prefixWord ++ tailWord_4786942).sum := by decide
  have hdescent : baseEnd_4786942 < baseStart_4786942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786954 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_4786954 : Nat := 118140960795 + 4786954 * 2 ^ 59
def prefixEnd_4786954 : Nat := 4983230072969 + 3 ^ 40 * 4786954 * 2
def baseEnd_4786954 : Nat := 819336090987589751386735

theorem tailTrace_4786954 : CollatzResearch.WordTrace tailWord_4786954 prefixEnd_4786954 819336090987589751386735 := by
  unfold tailWord_4786954
  simp only [CollatzResearch.WordTrace]
  refine ⟨43648638974922669875023979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116396370599793786333397277 43648638974922669875023979)
  ·
    refine ⟨65472958462384004812535969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43648638974922669875023979 65472958462384004812535969)
    ·
      refine ⟨49104718846788003609401977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65472958462384004812535969 49104718846788003609401977)
      ·
        refine ⟨36828539135091002707051483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49104718846788003609401977 36828539135091002707051483)
        ·
          refine ⟨55242808702636504060577225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36828539135091002707051483 55242808702636504060577225)
          ·
            refine ⟨41432106526977378045432919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55242808702636504060577225 41432106526977378045432919)
            ·
              refine ⟨62148159790466067068149379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41432106526977378045432919 62148159790466067068149379)
              ·
                refine ⟨93222239685699100602224069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62148159790466067068149379 93222239685699100602224069)
                ·
                  refine ⟨17479169941068581362917013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93222239685699100602224069 17479169941068581362917013)
                  ·
                    refine ⟨819336090987589751386735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17479169941068581362917013 819336090987589751386735)
                    ·
                      rfl

theorem cell23_4786954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_4786954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786954 prefixEnd_4786954 := by exact prefixLift 4786954
  have htrace : WordTrace (prefixWord ++ tailWord_4786954) baseStart_4786954 baseEnd_4786954 := by
    simpa [prefixWord, tailWord_4786954, baseEnd_4786954] using wordTrace_append hprefix tailTrace_4786954
  have hstable : (prefixWord ++ tailWord_4786954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786954).length < 2 ^ (prefixWord ++ tailWord_4786954).sum := by decide
  have hdescent : baseEnd_4786954 < baseStart_4786954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4786961 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 3, 4, 2]
def baseStart_4786961 : Nat := 118140960795 + 4786961 * 2 ^ 59
def prefixEnd_4786961 : Nat := 4983230072969 + 3 ^ 40 * 4786961 * 2
def baseEnd_4786961 : Nat := 2458011867327350726772673

theorem tailTrace_4786961 : CollatzResearch.WordTrace tailWord_4786961 prefixEnd_4786961 2458011867327350726772673 := by
  unfold tailWord_4786961
  simp only [CollatzResearch.WordTrace]
  refine ⟨174594811210665319695600737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116396540807110213130400491 174594811210665319695600737)
  ·
    refine ⟨130946108407998989771700553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174594811210665319695600737 130946108407998989771700553)
    ·
      refine ⟨98209581305999242328775415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130946108407998989771700553 98209581305999242328775415)
      ·
        refine ⟨147314371958998863493163123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98209581305999242328775415 147314371958998863493163123)
        ·
          refine ⟨220971557938498295239744685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147314371958998863493163123 220971557938498295239744685)
          ·
            refine ⟨82864334226936860714904257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220971557938498295239744685 82864334226936860714904257)
            ·
              refine ⟨62148250670202645536178193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82864334226936860714904257 62148250670202645536178193)
              ·
                refine ⟨46611188002651984152133645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62148250670202645536178193 46611188002651984152133645)
                ·
                  refine ⟨17479195500994494057050117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46611188002651984152133645 17479195500994494057050117)
                  ·
                    refine ⟨3277349156436467635696897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17479195500994494057050117 3277349156436467635696897)
                    ·
                      refine ⟨2458011867327350726772673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277349156436467635696897 2458011867327350726772673)
                      ·
                        rfl

theorem cell23_4786961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_4786961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4786961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4786961 prefixEnd_4786961 := by exact prefixLift 4786961
  have htrace : WordTrace (prefixWord ++ tailWord_4786961) baseStart_4786961 baseEnd_4786961 := by
    simpa [prefixWord, tailWord_4786961, baseEnd_4786961] using wordTrace_append hprefix tailTrace_4786961
  have hstable : (prefixWord ++ tailWord_4786961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4786961).length < 2 ^ (prefixWord ++ tailWord_4786961).sum := by decide
  have hdescent : baseEnd_4786961 < baseStart_4786961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4786961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787024 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_4787024 : Nat := 118140960795 + 4787024 * 2 ^ 59
def prefixEnd_4787024 : Nat := 4983230072969 + 3 ^ 40 * 4787024 * 2
def baseEnd_4787024 : Nat := 2458044216608583980284883

theorem tailTrace_4787024 : CollatzResearch.WordTrace tailWord_4787024 prefixEnd_4787024 2458044216608583980284883 := by
  unfold tailWord_4787024
  simp only [CollatzResearch.WordTrace]
  refine ⟨87298554504718540727572063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116398072672958054303429417 87298554504718540727572063)
  ·
    refine ⟨130947831757077811091358095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87298554504718540727572063 130947831757077811091358095)
    ·
      refine ⟨196421747635616716637037143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130947831757077811091358095 196421747635616716637037143)
      ·
        refine ⟨294632621453425074955555715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196421747635616716637037143 294632621453425074955555715)
        ·
          refine ⟨441948932180137612433333573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294632621453425074955555715 441948932180137612433333573)
          ·
            refine ⟨82865424783775802331250045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 441948932180137612433333573 82865424783775802331250045)
            ·
              refine ⟨31074534293915925874218767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82865424783775802331250045 31074534293915925874218767)
              ·
                refine ⟨46611801440873888811328151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31074534293915925874218767 46611801440873888811328151)
                ·
                  refine ⟨69917702161310833216992227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46611801440873888811328151 69917702161310833216992227)
                  ·
                    refine ⟨104876553241966249825488341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69917702161310833216992227 104876553241966249825488341)
                    ·
                      refine ⟨2458044216608583980284883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104876553241966249825488341 2458044216608583980284883)
                      ·
                        rfl

theorem cell23_4787024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_4787024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787024 prefixEnd_4787024 := by exact prefixLift 4787024
  have htrace : WordTrace (prefixWord ++ tailWord_4787024) baseStart_4787024 baseEnd_4787024 := by
    simpa [prefixWord, tailWord_4787024, baseEnd_4787024] using wordTrace_append hprefix tailTrace_4787024
  have hstable : (prefixWord ++ tailWord_4787024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787024).length < 2 ^ (prefixWord ++ tailWord_4787024).sum := by decide
  have hdescent : baseEnd_4787024 < baseStart_4787024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787048 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 2, 5]
def baseStart_4787048 : Nat := 118140960795 + 4787048 * 2 ^ 59
def prefixEnd_4787048 : Nat := 4983230072969 + 3 ^ 40 * 4787048 * 2
def baseEnd_4787048 : Nat := 819352180048097295461591

theorem tailTrace_4787048 : CollatzResearch.WordTrace tailWord_4787048 prefixEnd_4787048 819352180048097295461591 := by
  unfold tailWord_4787048
  simp only [CollatzResearch.WordTrace]
  refine ⟨87298992180675066777008899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116398656240900089036011865 87298992180675066777008899)
  ·
    refine ⟨130948488271012600165513349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87298992180675066777008899 130948488271012600165513349)
    ·
      refine ⟨24552841550814862531033753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130948488271012600165513349 24552841550814862531033753)
      ·
        refine ⟨18414631163111146898275315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24552841550814862531033753 18414631163111146898275315)
        ·
          refine ⟨27621946744666720347412973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18414631163111146898275315 27621946744666720347412973)
          ·
            refine ⟨10358230029250020130279865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27621946744666720347412973 10358230029250020130279865)
            ·
              refine ⟨7768672521937515097709899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10358230029250020130279865 7768672521937515097709899)
              ·
                refine ⟨11653008782906272646564849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7768672521937515097709899 11653008782906272646564849)
                ·
                  refine ⟨8739756587179704484923637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11653008782906272646564849 8739756587179704484923637)
                  ·
                    refine ⟨819352180048097295461591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8739756587179704484923637 819352180048097295461591)
                    ·
                      rfl

theorem cell23_4787048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_4787048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787048 prefixEnd_4787048 := by exact prefixLift 4787048
  have htrace : WordTrace (prefixWord ++ tailWord_4787048) baseStart_4787048 baseEnd_4787048 := by
    simpa [prefixWord, tailWord_4787048, baseEnd_4787048] using wordTrace_append hprefix tailTrace_4787048
  have hstable : (prefixWord ++ tailWord_4787048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787048).length < 2 ^ (prefixWord ++ tailWord_4787048).sum := by decide
  have hdescent : baseEnd_4787048 < baseStart_4787048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787051 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 4]
def baseStart_4787051 : Nat := 118140960795 + 4787051 * 2 ^ 59
def prefixEnd_4787051 : Nat := 4983230072969 + 3 ^ 40 * 4787051 * 2
def baseEnd_4787051 : Nat := 2458058080586255374647259

theorem tailTrace_4787051 : CollatzResearch.WordTrace tailWord_4787051 prefixEnd_4787051 2458058080586255374647259 := by
  unfold tailWord_4787051
  simp only [CollatzResearch.WordTrace]
  refine ⟨174598093780339265066377007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116398729186892843377584671 174598093780339265066377007)
  ·
    refine ⟨261897140670508897599565511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174598093780339265066377007 261897140670508897599565511)
    ·
      refine ⟨392845711005763346399348267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261897140670508897599565511 392845711005763346399348267)
      ·
        refine ⟨589268566508645019599022401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392845711005763346399348267 589268566508645019599022401)
        ·
          refine ⟨441951424881483764699266801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589268566508645019599022401 441951424881483764699266801)
          ·
            refine ⟨331463568661112823524450101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441951424881483764699266801 331463568661112823524450101)
            ·
              refine ⟨31074709561979327205417197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 331463568661112823524450101 31074709561979327205417197)
              ·
                refine ⟨11653016085742247702031449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31074709561979327205417197 11653016085742247702031449)
                ·
                  refine ⟨8739762064306685776523587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11653016085742247702031449 8739762064306685776523587)
                  ·
                    refine ⟨13109643096460028664785381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8739762064306685776523587 13109643096460028664785381)
                    ·
                      refine ⟨2458058080586255374647259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13109643096460028664785381 2458058080586255374647259)
                      ·
                        rfl

theorem cell23_4787051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 4].length) (baseStart_4787051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787051 prefixEnd_4787051 := by exact prefixLift 4787051
  have htrace : WordTrace (prefixWord ++ tailWord_4787051) baseStart_4787051 baseEnd_4787051 := by
    simpa [prefixWord, tailWord_4787051, baseEnd_4787051] using wordTrace_append hprefix tailTrace_4787051
  have hstable : (prefixWord ++ tailWord_4787051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787051).length < 2 ^ (prefixWord ++ tailWord_4787051).sum := by decide
  have hdescent : baseEnd_4787051 < baseStart_4787051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787105 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4787105 : Nat := 118140960795 + 4787105 * 2 ^ 59
def prefixEnd_4787105 : Nat := 4983230072969 + 3 ^ 40 * 4787105 * 2
def baseEnd_4787105 : Nat := 2458085808541598163372011

theorem tailTrace_4787105 : CollatzResearch.WordTrace tailWord_4787105 prefixEnd_4787105 2458085808541598163372011 := by
  unfold tailWord_4787105
  simp only [CollatzResearch.WordTrace]
  refine ⟨174600063322143632288842769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116400042214762421525895179 174600063322143632288842769)
  ·
    refine ⟨130950047491607724216632077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174600063322143632288842769 130950047491607724216632077)
    ·
      refine ⟨49106267809352896581237029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130950047491607724216632077 49106267809352896581237029)
      ·
        refine ⟨9207425214253668108981943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49106267809352896581237029 9207425214253668108981943)
        ·
          refine ⟨13811137821380502163472915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9207425214253668108981943 13811137821380502163472915)
          ·
            refine ⟨20716706732070753245209373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13811137821380502163472915 20716706732070753245209373)
            ·
              refine ⟨7768765024526532466953515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20716706732070753245209373 7768765024526532466953515)
              ·
                refine ⟨11653147536789798700430273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7768765024526532466953515 11653147536789798700430273)
                ·
                  refine ⟨8739860652592349025322705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11653147536789798700430273 8739860652592349025322705)
                  ·
                    refine ⟨6554895489444261768992029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8739860652592349025322705 6554895489444261768992029)
                    ·
                      refine ⟨2458085808541598163372011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6554895489444261768992029 2458085808541598163372011)
                      ·
                        rfl

theorem cell23_4787105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4787105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787105 prefixEnd_4787105 := by exact prefixLift 4787105
  have htrace : WordTrace (prefixWord ++ tailWord_4787105) baseStart_4787105 baseEnd_4787105 := by
    simpa [prefixWord, tailWord_4787105, baseEnd_4787105] using wordTrace_append hprefix tailTrace_4787105
  have hstable : (prefixWord ++ tailWord_4787105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787105).length < 2 ^ (prefixWord ++ tailWord_4787105).sum := by decide
  have hdescent : baseEnd_4787105 < baseStart_4787105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787175 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_4787175 : Nat := 118140960795 + 4787175 * 2 ^ 59
def prefixEnd_4787175 : Nat := 4983230072969 + 3 ^ 40 * 4787175 * 2
def baseEnd_4787175 : Nat := 2458121752187412889496689

theorem tailTrace_4787175 : CollatzResearch.WordTrace tailWord_4787175 prefixEnd_4787175 2458121752187412889496689 := by
  unfold tailWord_4787175
  simp only [CollatzResearch.WordTrace]
  refine ⟨174602616431890034243890979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116401744287926689495927319 174602616431890034243890979)
  ·
    refine ⟨261903924647835051365836469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174602616431890034243890979 261903924647835051365836469)
    ·
      refine ⟨24553492935734536065547169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261903924647835051365836469 24553492935734536065547169)
      ·
        refine ⟨18415119701800902049160377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24553492935734536065547169 18415119701800902049160377)
        ·
          refine ⟨13811339776350676536870283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18415119701800902049160377 13811339776350676536870283)
          ·
            refine ⟨20717009664526014805305425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13811339776350676536870283 20717009664526014805305425)
            ·
              refine ⟨15537757248394511103979069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20717009664526014805305425 15537757248394511103979069)
              ·
                refine ⟨5826658968147941663992151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15537757248394511103979069 5826658968147941663992151)
                ·
                  refine ⟨8739988452221912495988227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826658968147941663992151 8739988452221912495988227)
                  ·
                    refine ⟨13109982678332868743982341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8739988452221912495988227 13109982678332868743982341)
                    ·
                      refine ⟨2458121752187412889496689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13109982678332868743982341 2458121752187412889496689)
                      ·
                        rfl

theorem cell23_4787175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_4787175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787175 prefixEnd_4787175 := by exact prefixLift 4787175
  have htrace : WordTrace (prefixWord ++ tailWord_4787175) baseStart_4787175 baseEnd_4787175 := by
    simpa [prefixWord, tailWord_4787175, baseEnd_4787175] using wordTrace_append hprefix tailTrace_4787175
  have hstable : (prefixWord ++ tailWord_4787175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787175).length < 2 ^ (prefixWord ++ tailWord_4787175).sum := by decide
  have hdescent : baseEnd_4787175 < baseStart_4787175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787178 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_4787178 : Nat := 118140960795 + 4787178 * 2 ^ 59
def prefixEnd_4787178 : Nat := 4983230072969 + 3 ^ 40 * 4787178 * 2
def baseEnd_4787178 : Nat := 2458123292629376377759175

theorem tailTrace_4787178 : CollatzResearch.WordTrace tailWord_4787178 prefixEnd_4787178 2458123292629376377759175 := by
  unfold tailWord_4787178
  simp only [CollatzResearch.WordTrace]
  refine ⟨43650681462719791439062547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116401817233919443837500125 43650681462719791439062547)
  ·
    refine ⟨65476022194079687158593821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43650681462719791439062547 65476022194079687158593821)
    ·
      refine ⟨24553508322779882684472683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65476022194079687158593821 24553508322779882684472683)
      ·
        refine ⟨36830262484169824026709025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24553508322779882684472683 36830262484169824026709025)
        ·
          refine ⟨27622696863127368020031769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36830262484169824026709025 27622696863127368020031769)
          ·
            refine ⟨20717022647345526015023827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27622696863127368020031769 20717022647345526015023827)
            ·
              refine ⟨31075533971018289022535741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20717022647345526015023827 31075533971018289022535741)
              ·
                refine ⟨11653325239131858383450903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31075533971018289022535741 11653325239131858383450903)
                ·
                  refine ⟨17479987858697787575176355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11653325239131858383450903 17479987858697787575176355)
                  ·
                    refine ⟨26219981788046681362764533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17479987858697787575176355 26219981788046681362764533)
                    ·
                      refine ⟨2458123292629376377759175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26219981788046681362764533 2458123292629376377759175)
                      ·
                        rfl

theorem cell23_4787178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_4787178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787178 prefixEnd_4787178 := by exact prefixLift 4787178
  have htrace : WordTrace (prefixWord ++ tailWord_4787178) baseStart_4787178 baseEnd_4787178 := by
    simpa [prefixWord, tailWord_4787178, baseEnd_4787178] using wordTrace_append hprefix tailTrace_4787178
  have hstable : (prefixWord ++ tailWord_4787178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787178).length < 2 ^ (prefixWord ++ tailWord_4787178).sum := by decide
  have hdescent : baseEnd_4787178 < baseStart_4787178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787186 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4787186 : Nat := 118140960795 + 4787186 * 2 ^ 59
def prefixEnd_4787186 : Nat := 4983230072969 + 3 ^ 40 * 4787186 * 2
def baseEnd_4787186 : Nat := 2458127400474612346459139

theorem tailTrace_4787186 : CollatzResearch.WordTrace tailWord_4787186 prefixEnd_4787186 2458127400474612346459139 := by
  unfold tailWord_4787186
  simp only [CollatzResearch.WordTrace]
  refine ⟨43650754408712545780635353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116402011756566788748360941 43650754408712545780635353)
  ·
    refine ⟨32738065806534409335476515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43650754408712545780635353 32738065806534409335476515)
    ·
      refine ⟨49107098709801614003214773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32738065806534409335476515 49107098709801614003214773)
      ·
        refine ⟨4603790504043901312801385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49107098709801614003214773 4603790504043901312801385)
        ·
          refine ⟨3452842878032925984601039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4603790504043901312801385 3452842878032925984601039)
          ·
            refine ⟨5179264317049388976901559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452842878032925984601039 5179264317049388976901559)
            ·
              refine ⟨7768896475574083465352339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5179264317049388976901559 7768896475574083465352339)
              ·
                refine ⟨11653344713361125198028509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7768896475574083465352339 11653344713361125198028509)
                ·
                  refine ⟨4370004267510421949260691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11653344713361125198028509 4370004267510421949260691)
                  ·
                    refine ⟨6555006401265632923891037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4370004267510421949260691 6555006401265632923891037)
                    ·
                      refine ⟨2458127400474612346459139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6555006401265632923891037 2458127400474612346459139)
                      ·
                        rfl

theorem cell23_4787186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4787186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787186 prefixEnd_4787186 := by exact prefixLift 4787186
  have htrace : WordTrace (prefixWord ++ tailWord_4787186) baseStart_4787186 baseEnd_4787186 := by
    simpa [prefixWord, tailWord_4787186, baseEnd_4787186] using wordTrace_append hprefix tailTrace_4787186
  have hstable : (prefixWord ++ tailWord_4787186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787186).length < 2 ^ (prefixWord ++ tailWord_4787186).sum := by decide
  have hdescent : baseEnd_4787186 < baseStart_4787186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787212 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_4787212 : Nat := 118140960795 + 4787212 * 2 ^ 59
def prefixEnd_4787212 : Nat := 4983230072969 + 3 ^ 40 * 4787212 * 2
def baseEnd_4787212 : Nat := 2458140750971629244734019

theorem tailTrace_4787212 : CollatzResearch.WordTrace tailWord_4787212 prefixEnd_4787212 2458140750971629244734019 := by
  unfold tailWord_4787212
  simp only [CollatzResearch.WordTrace]
  refine ⟨87301982966377994781493945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116402643955170659708658593 87301982966377994781493945)
  ·
    refine ⟨65476487224783496086120459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87301982966377994781493945 65476487224783496086120459)
    ·
      refine ⟨98214730837175244129180689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65476487224783496086120459 98214730837175244129180689)
      ·
        refine ⟨73661048127881433096885517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98214730837175244129180689 73661048127881433096885517)
        ·
          refine ⟨27622893047955537411332069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73661048127881433096885517 27622893047955537411332069)
          ·
            refine ⟨5179292446491663264624763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27622893047955537411332069 5179292446491663264624763)
            ·
              refine ⟨7768938669737494896937145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5179292446491663264624763 7768938669737494896937145)
              ·
                refine ⟨5826704002303121172702859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7768938669737494896937145 5826704002303121172702859)
                ·
                  refine ⟨8740056003454681759054289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826704002303121172702859 8740056003454681759054289)
                  ·
                    refine ⟨6555042002591011319290717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8740056003454681759054289 6555042002591011319290717)
                    ·
                      refine ⟨2458140750971629244734019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6555042002591011319290717 2458140750971629244734019)
                      ·
                        rfl

theorem cell23_4787212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_4787212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787212 prefixEnd_4787212 := by exact prefixLift 4787212
  have htrace : WordTrace (prefixWord ++ tailWord_4787212) baseStart_4787212 baseEnd_4787212 := by
    simpa [prefixWord, tailWord_4787212, baseEnd_4787212] using wordTrace_append hprefix tailTrace_4787212
  have hstable : (prefixWord ++ tailWord_4787212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787212).length < 2 ^ (prefixWord ++ tailWord_4787212).sum := by decide
  have hdescent : baseEnd_4787212 < baseStart_4787212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787229 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_4787229 : Nat := 118140960795 + 4787229 * 2 ^ 59
def prefixEnd_4787229 : Nat := 4983230072969 + 3 ^ 40 * 4787229 * 2
def baseEnd_4787229 : Nat := 2458149480142755678221441

theorem tailTrace_4787229 : CollatzResearch.WordTrace tailWord_4787229 prefixEnd_4787229 2458149480142755678221441 := by
  unfold tailWord_4787229
  simp only [CollatzResearch.WordTrace]
  refine ⟨174604585973694401466356741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116403057315796267644237827 174604585973694401466356741)
  ·
    refine ⟨32738359870067700274941889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174604585973694401466356741 32738359870067700274941889)
    ·
      refine ⟨24553769902550775206206417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32738359870067700274941889 24553769902550775206206417)
      ·
        refine ⟨18415327426913081404654813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24553769902550775206206417 18415327426913081404654813)
        ·
          refine ⟨6905747785092405526745555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18415327426913081404654813 6905747785092405526745555)
          ·
            refine ⟨10358621677638608290118333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6905747785092405526745555 10358621677638608290118333)
            ·
              refine ⟨3884483129114478108794375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10358621677638608290118333 3884483129114478108794375)
              ·
                refine ⟨5826724693671717163191563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884483129114478108794375 5826724693671717163191563)
                ·
                  refine ⟨8740087040507575744787345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826724693671717163191563 8740087040507575744787345)
                  ·
                    refine ⟨6555065280380681808590509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8740087040507575744787345 6555065280380681808590509)
                    ·
                      refine ⟨2458149480142755678221441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6555065280380681808590509 2458149480142755678221441)
                      ·
                        rfl

theorem cell23_4787229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_4787229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787229 prefixEnd_4787229 := by exact prefixLift 4787229
  have htrace : WordTrace (prefixWord ++ tailWord_4787229) baseStart_4787229 baseEnd_4787229 := by
    simpa [prefixWord, tailWord_4787229, baseEnd_4787229] using wordTrace_append hprefix tailTrace_4787229
  have hstable : (prefixWord ++ tailWord_4787229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787229).length < 2 ^ (prefixWord ++ tailWord_4787229).sum := by decide
  have hdescent : baseEnd_4787229 < baseStart_4787229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787278 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_4787278 : Nat := 118140960795 + 4787278 * 2 ^ 59
def prefixEnd_4787278 : Nat := 4983230072969 + 3 ^ 40 * 4787278 * 2
def baseEnd_4787278 : Nat := 2458174640694825986508715

theorem tailTrace_4787278 : CollatzResearch.WordTrace tailWord_4787278 prefixEnd_4787278 2458174640694825986508715 := by
  unfold tailWord_4787278
  simp only [CollatzResearch.WordTrace]
  refine ⟨21825796643814610354361311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116404248767011255223260325 21825796643814610354361311)
  ·
    refine ⟨32738694965721915531541967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21825796643814610354361311 32738694965721915531541967)
    ·
      refine ⟨49108042448582873297312951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32738694965721915531541967 49108042448582873297312951)
      ·
        refine ⟨73662063672874309945969427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49108042448582873297312951 73662063672874309945969427)
        ·
          refine ⟨110493095509311464918954141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73662063672874309945969427 110493095509311464918954141)
          ·
            refine ⟨41434910815991799344607803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110493095509311464918954141 41434910815991799344607803)
            ·
              refine ⟨62152366223987699016911705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41434910815991799344607803 62152366223987699016911705)
              ·
                refine ⟨46614274667990774262683779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62152366223987699016911705 46614274667990774262683779)
                ·
                  refine ⟨69921412001986161394025669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46614274667990774262683779 69921412001986161394025669)
                  ·
                    refine ⟨13110264750372405261379813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69921412001986161394025669 13110264750372405261379813)
                    ·
                      refine ⟨2458174640694825986508715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13110264750372405261379813 2458174640694825986508715)
                      ·
                        rfl

theorem cell23_4787278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_4787278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787278 prefixEnd_4787278 := by exact prefixLift 4787278
  have htrace : WordTrace (prefixWord ++ tailWord_4787278) baseStart_4787278 baseEnd_4787278 := by
    simpa [prefixWord, tailWord_4787278, baseEnd_4787278] using wordTrace_append hprefix tailTrace_4787278
  have hstable : (prefixWord ++ tailWord_4787278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787278).length < 2 ^ (prefixWord ++ tailWord_4787278).sum := by decide
  have hdescent : baseEnd_4787278 < baseStart_4787278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787282 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_4787282 : Nat := 118140960795 + 4787282 * 2 ^ 59
def prefixEnd_4787282 : Nat := 4983230072969 + 3 ^ 40 * 4787282 * 2
def baseEnd_4787282 : Nat := 2458176694617443970858697

theorem tailTrace_4787282 : CollatzResearch.WordTrace tailWord_4787282 prefixEnd_4787282 2458176694617443970858697 := by
  unfold tailWord_4787282
  simp only [CollatzResearch.WordTrace]
  refine ⟨43651629760625597879509025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116404346028334927678690733 43651629760625597879509025)
  ·
    refine ⟨32738722320469198409631769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43651629760625597879509025 32738722320469198409631769)
    ·
      refine ⟨24554041740351898807223827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32738722320469198409631769 24554041740351898807223827)
      ·
        refine ⟨36831062610527848210835741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24554041740351898807223827 36831062610527848210835741)
        ·
          refine ⟨13811648478947943079063403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36831062610527848210835741 13811648478947943079063403)
          ·
            refine ⟨20717472718421914618595105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13811648478947943079063403 20717472718421914618595105)
            ·
              refine ⟨15538104538816435963946329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20717472718421914618595105 15538104538816435963946329)
              ·
                refine ⟨11653578404112326972959747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15538104538816435963946329 11653578404112326972959747)
                ·
                  refine ⟨17480367606168490459439621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11653578404112326972959747 17480367606168490459439621)
                  ·
                    refine ⟨3277568926156591961144929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17480367606168490459439621 3277568926156591961144929)
                    ·
                      refine ⟨2458176694617443970858697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277568926156591961144929 2458176694617443970858697)
                      ·
                        rfl

theorem cell23_4787282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_4787282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787282 prefixEnd_4787282 := by exact prefixLift 4787282
  have htrace : WordTrace (prefixWord ++ tailWord_4787282) baseStart_4787282 baseEnd_4787282 := by
    simpa [prefixWord, tailWord_4787282, baseEnd_4787282] using wordTrace_append hprefix tailTrace_4787282
  have hstable : (prefixWord ++ tailWord_4787282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787282).length < 2 ^ (prefixWord ++ tailWord_4787282).sum := by decide
  have hdescent : baseEnd_4787282 < baseStart_4787282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787293 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4787293 : Nat := 118140960795 + 4787293 * 2 ^ 59
def prefixEnd_4787293 : Nat := 4983230072969 + 3 ^ 40 * 4787293 * 2
def baseEnd_4787293 : Nat := 2458182342904643427821147

theorem tailTrace_4787293 : CollatzResearch.WordTrace tailWord_4787293 prefixEnd_4787293 2458182342904643427821147 := by
  unfold tailWord_4787293
  simp only [CollatzResearch.WordTrace]
  refine ⟨174606920245462540396686533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116404613496975026931124355 174606920245462540396686533)
  ·
    refine ⟨32738797546024226324378725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174606920245462540396686533 32738797546024226324378725)
    ·
      refine ⟨6138524539879542435821011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32738797546024226324378725 6138524539879542435821011)
      ·
        refine ⟨9207786809819313653731517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6138524539879542435821011 9207786809819313653731517)
        ·
          refine ⟨3452920053682242620149319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9207786809819313653731517 3452920053682242620149319)
          ·
            refine ⟨5179380080523363930223979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452920053682242620149319 5179380080523363930223979)
            ·
              refine ⟨7769070120785045895335969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5179380080523363930223979 7769070120785045895335969)
              ·
                refine ⟨5826802590588784421501977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7769070120785045895335969 5826802590588784421501977)
                ·
                  refine ⟨4370101942941588316126483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5826802590588784421501977 4370101942941588316126483)
                  ·
                    refine ⟨6555152914412382474189725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4370101942941588316126483 6555152914412382474189725)
                    ·
                      refine ⟨2458182342904643427821147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6555152914412382474189725 2458182342904643427821147)
                      ·
                        rfl

theorem cell23_4787293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4787293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787293 prefixEnd_4787293 := by exact prefixLift 4787293
  have htrace : WordTrace (prefixWord ++ tailWord_4787293) baseStart_4787293 baseEnd_4787293 := by
    simpa [prefixWord, tailWord_4787293, baseEnd_4787293] using wordTrace_append hprefix tailTrace_4787293
  have hstable : (prefixWord ++ tailWord_4787293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787293).length < 2 ^ (prefixWord ++ tailWord_4787293).sum := by decide
  have hdescent : baseEnd_4787293 < baseStart_4787293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787305 : List Nat := [1, 2, 1, 1, 1, 6, 2, 4, 5]
def baseStart_4787305 : Nat := 118140960795 + 4787305 * 2 ^ 59
def prefixEnd_4787305 : Nat := 4983230072969 + 3 ^ 40 * 4787305 * 2
def baseEnd_4787305 : Nat := 273132056074721931207899

theorem tailTrace_4787305 : CollatzResearch.WordTrace tailWord_4787305 prefixEnd_4787305 273132056074721931207899 := by
  unfold tailWord_4787305
  simp only [CollatzResearch.WordTrace]
  refine ⟨174607357921419066446123369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116404905280946044297415579 174607357921419066446123369)
  ·
    refine ⟨130955518441064299834592527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174607357921419066446123369 130955518441064299834592527)
    ·
      refine ⟨196433277661596449751888791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130955518441064299834592527 196433277661596449751888791)
      ·
        refine ⟨294649916492394674627833187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196433277661596449751888791 294649916492394674627833187)
        ·
          refine ⟨441974874738592011941749781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294649916492394674627833187 441974874738592011941749781)
          ·
            refine ⟨20717572253371500559769521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 441974874738592011941749781 20717572253371500559769521)
            ·
              refine ⟨15538179190028625419827141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20717572253371500559769521 15538179190028625419827141)
              ·
                refine ⟨2913408598130367266217589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15538179190028625419827141 2913408598130367266217589)
                ·
                  refine ⟨273132056074721931207899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2913408598130367266217589 273132056074721931207899)
                  ·
                    rfl

theorem cell23_4787305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 5].length) (baseStart_4787305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787305 prefixEnd_4787305 := by exact prefixLift 4787305
  have htrace : WordTrace (prefixWord ++ tailWord_4787305) baseStart_4787305 baseEnd_4787305 := by
    simpa [prefixWord, tailWord_4787305, baseEnd_4787305] using wordTrace_append hprefix tailTrace_4787305
  have hstable : (prefixWord ++ tailWord_4787305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787305).length < 2 ^ (prefixWord ++ tailWord_4787305).sum := by decide
  have hdescent : baseEnd_4787305 < baseStart_4787305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787362 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4787362 : Nat := 118140960795 + 4787362 * 2 ^ 59
def prefixEnd_4787362 : Nat := 4983230072969 + 3 ^ 40 * 4787362 * 2
def baseEnd_4787362 : Nat := 2458217773069803657858329

theorem tailTrace_4787362 : CollatzResearch.WordTrace tailWord_4787362 prefixEnd_4787362 2458217773069803657858329 := by
  unfold tailWord_4787362
  simp only [CollatzResearch.WordTrace]
  refine ⟨43652359220553141295237085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116406291254808376787298893 43652359220553141295237085)
  ·
    refine ⟨16369634707707427985713907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43652359220553141295237085 16369634707707427985713907)
    ·
      refine ⟨24554452061561141978570861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16369634707707427985713907 24554452061561141978570861)
      ·
        refine ⟨9207919523085428241964073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24554452061561141978570861 9207919523085428241964073)
        ·
          refine ⟨6905939642314071181473055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9207919523085428241964073 6905939642314071181473055)
          ·
            refine ⟨10358909463471106772209583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6905939642314071181473055 10358909463471106772209583)
            ·
              refine ⟨15538364195206660158314375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10358909463471106772209583 15538364195206660158314375)
              ·
                refine ⟨23307546292809990237471563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15538364195206660158314375 23307546292809990237471563)
                ·
                  refine ⟨34961319439214985356207345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23307546292809990237471563 34961319439214985356207345)
                  ·
                    refine ⟨26220989579411239017155509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34961319439214985356207345 26220989579411239017155509)
                    ·
                      refine ⟨2458217773069803657858329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26220989579411239017155509 2458217773069803657858329)
                      ·
                        rfl

theorem cell23_4787362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4787362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787362 prefixEnd_4787362 := by exact prefixLift 4787362
  have htrace : WordTrace (prefixWord ++ tailWord_4787362) baseStart_4787362 baseEnd_4787362 := by
    simpa [prefixWord, tailWord_4787362, baseEnd_4787362] using wordTrace_append hprefix tailTrace_4787362
  have hstable : (prefixWord ++ tailWord_4787362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787362).length < 2 ^ (prefixWord ++ tailWord_4787362).sum := by decide
  have hdescent : baseEnd_4787362 < baseStart_4787362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787425 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 3, 5]
def baseStart_4787425 : Nat := 118140960795 + 4787425 * 2 ^ 59
def prefixEnd_4787425 : Nat := 4983230072969 + 3 ^ 40 * 4787425 * 2
def baseEnd_4787425 : Nat := 819416707450345637123513

theorem tailTrace_4787425 : CollatzResearch.WordTrace tailWord_4787425 prefixEnd_4787425 819416707450345637123513 := by
  unfold tailWord_4787425
  simp only [CollatzResearch.WordTrace]
  refine ⟨174611734680984326940491729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116407823120656217960327819 174611734680984326940491729)
  ·
    refine ⟨130958801010738245205368797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174611734680984326940491729 130958801010738245205368797)
    ·
      refine ⟨49109550379026841952013299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130958801010738245205368797 49109550379026841952013299)
      ·
        refine ⟨73664325568540262928019949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49109550379026841952013299 73664325568540262928019949)
        ·
          refine ⟨27624122088202598598007481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73664325568540262928019949 27624122088202598598007481)
          ·
            refine ⟨20718091566151948948505611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27624122088202598598007481 20718091566151948948505611)
            ·
              refine ⟨31077137349227923422758417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20718091566151948948505611 31077137349227923422758417)
              ·
                refine ⟨23307853011920942567068813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31077137349227923422758417 23307853011920942567068813)
                ·
                  refine ⟨8740444879470353462650805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23307853011920942567068813 8740444879470353462650805)
                  ·
                    refine ⟨819416707450345637123513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8740444879470353462650805 819416707450345637123513)
                    ·
                      rfl

theorem cell23_4787425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_4787425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787425 prefixEnd_4787425 := by exact prefixLift 4787425
  have htrace : WordTrace (prefixWord ++ tailWord_4787425) baseStart_4787425 baseEnd_4787425 := by
    simpa [prefixWord, tailWord_4787425, baseEnd_4787425] using wordTrace_append hprefix tailTrace_4787425
  have hstable : (prefixWord ++ tailWord_4787425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787425).length < 2 ^ (prefixWord ++ tailWord_4787425).sum := by decide
  have hdescent : baseEnd_4787425 < baseStart_4787425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787432 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_4787432 : Nat := 118140960795 + 4787432 * 2 ^ 59
def prefixEnd_4787432 : Nat := 4983230072969 + 3 ^ 40 * 4787432 * 2
def baseEnd_4787432 : Nat := 2458253716715618383983007

theorem tailTrace_4787432 : CollatzResearch.WordTrace tailWord_4787432 prefixEnd_4787432 2458253716715618383983007 := by
  unfold tailWord_4787432
  simp only [CollatzResearch.WordTrace]
  refine ⟨87305994995979483567998275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116407993327972644757331033 87305994995979483567998275)
  ·
    refine ⟨130958992493969225351997413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87305994995979483567998275 130958992493969225351997413)
    ·
      refine ⟨24554811092619229753499515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130958992493969225351997413 24554811092619229753499515)
      ·
        refine ⟨36832216638928844630249273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24554811092619229753499515 36832216638928844630249273)
        ·
          refine ⟨27624162479196633472686955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36832216638928844630249273 27624162479196633472686955)
          ·
            refine ⟨41436243718794950209030433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27624162479196633472686955 41436243718794950209030433)
            ·
              refine ⟨31077182789096212656772825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41436243718794950209030433 31077182789096212656772825)
              ·
                refine ⟨23307887091822159492579619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31077182789096212656772825 23307887091822159492579619)
                ·
                  refine ⟨34961830637733239238869429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23307887091822159492579619 34961830637733239238869429)
                  ·
                    refine ⟨3277671622287491178644009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34961830637733239238869429 3277671622287491178644009)
                    ·
                      refine ⟨2458253716715618383983007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277671622287491178644009 2458253716715618383983007)
                      ·
                        rfl

theorem cell23_4787432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_4787432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787432 prefixEnd_4787432 := by exact prefixLift 4787432
  have htrace : WordTrace (prefixWord ++ tailWord_4787432) baseStart_4787432 baseEnd_4787432 := by
    simpa [prefixWord, tailWord_4787432, baseEnd_4787432] using wordTrace_append hprefix tailTrace_4787432
  have hstable : (prefixWord ++ tailWord_4787432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787432).length < 2 ^ (prefixWord ++ tailWord_4787432).sum := by decide
  have hdescent : baseEnd_4787432 < baseStart_4787432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787439 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 3]
def baseStart_4787439 : Nat := 118140960795 + 4787439 * 2 ^ 59
def prefixEnd_4787439 : Nat := 4983230072969 + 3 ^ 40 * 4787439 * 2
def baseEnd_4787439 : Nat := 2458257311080199856595475

theorem tailTrace_4787439 : CollatzResearch.WordTrace tailWord_4787439 prefixEnd_4787439 2458257311080199856595475 := by
  unfold tailWord_4787439
  simp only [CollatzResearch.WordTrace]
  refine ⟨174612245302933607331501371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116408163535289071554334247 174612245302933607331501371)
  ·
    refine ⟨261918367954400410997252057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174612245302933607331501371 261918367954400410997252057)
    ·
      refine ⟨196438775965800308247939043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261918367954400410997252057 196438775965800308247939043)
      ·
        refine ⟨294658163948700462371908565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196438775965800308247939043 294658163948700462371908565)
        ·
          refine ⟨6906050717547667086841607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 294658163948700462371908565 6906050717547667086841607)
          ·
            refine ⟨10359076076321500630262411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6906050717547667086841607 10359076076321500630262411)
            ·
              refine ⟨15538614114482250945393617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10359076076321500630262411 15538614114482250945393617)
              ·
                refine ⟨11653960585861688209045213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15538614114482250945393617 11653960585861688209045213)
                ·
                  refine ⟨4370235219698133078391955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11653960585861688209045213 4370235219698133078391955)
                  ·
                    refine ⟨6555352829547199617587933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4370235219698133078391955 6555352829547199617587933)
                    ·
                      refine ⟨2458257311080199856595475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6555352829547199617587933 2458257311080199856595475)
                      ·
                        rfl

theorem cell23_4787439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 3].length) (baseStart_4787439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787439 prefixEnd_4787439 := by exact prefixLift 4787439
  have htrace : WordTrace (prefixWord ++ tailWord_4787439) baseStart_4787439 baseEnd_4787439 := by
    simpa [prefixWord, tailWord_4787439, baseEnd_4787439] using wordTrace_append hprefix tailTrace_4787439
  have hstable : (prefixWord ++ tailWord_4787439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787439).length < 2 ^ (prefixWord ++ tailWord_4787439).sum := by decide
  have hdescent : baseEnd_4787439 < baseStart_4787439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787455 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 1, 6]
def baseStart_4787455 : Nat := 118140960795 + 4787455 * 2 ^ 59
def prefixEnd_4787455 : Nat := 4983230072969 + 3 ^ 40 * 4787455 * 2
def baseEnd_4787455 : Nat := 819421842256890597998467

theorem tailTrace_4787455 : CollatzResearch.WordTrace tailWord_4787455 prefixEnd_4787455 819421842256890597998467 := by
  unfold tailWord_4787455
  simp only [CollatzResearch.WordTrace]
  refine ⟨174612828870875642064083819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116408552580583761376055879 174612828870875642064083819)
  ·
    refine ⟨261919243306313463096125729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174612828870875642064083819 261919243306313463096125729)
    ·
      refine ⟨196439432479735097322094297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261919243306313463096125729 196439432479735097322094297)
      ·
        refine ⟨147329574359801322991570723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196439432479735097322094297 147329574359801322991570723)
        ·
          refine ⟨220994361539701984487356085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147329574359801322991570723 220994361539701984487356085)
          ·
            refine ⟨20718221394347061045689633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 220994361539701984487356085 20718221394347061045689633)
            ·
              refine ⟨15538666045760295784267225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20718221394347061045689633 15538666045760295784267225)
              ·
                refine ⟨11653999534320221838200419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15538666045760295784267225 11653999534320221838200419)
                ·
                  refine ⟨17480999301480332757300629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11653999534320221838200419 17480999301480332757300629)
                  ·
                    refine ⟨819421842256890597998467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17480999301480332757300629 819421842256890597998467)
                    ·
                      rfl

theorem cell23_4787455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_4787455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787455 prefixEnd_4787455 := by exact prefixLift 4787455
  have htrace : WordTrace (prefixWord ++ tailWord_4787455) baseStart_4787455 baseEnd_4787455 := by
    simpa [prefixWord, tailWord_4787455, baseEnd_4787455] using wordTrace_append hprefix tailTrace_4787455
  have hstable : (prefixWord ++ tailWord_4787455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787455).length < 2 ^ (prefixWord ++ tailWord_4787455).sum := by decide
  have hdescent : baseEnd_4787455 < baseStart_4787455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787459 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 1, 5]
def baseStart_4787459 : Nat := 118140960795 + 4787459 * 2 ^ 59
def prefixEnd_4787459 : Nat := 4983230072969 + 3 ^ 40 * 4787459 * 2
def baseEnd_4787459 : Nat := 819422526897763259448461

theorem tailTrace_4787459 : CollatzResearch.WordTrace tailWord_4787459 prefixEnd_4787459 819422526897763259448461 := by
  unfold tailWord_4787459
  simp only [CollatzResearch.WordTrace]
  refine ⟨174612974762861150747229431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116408649841907433831486287 174612974762861150747229431)
  ·
    refine ⟨261919462144291726120844147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174612974762861150747229431 261919462144291726120844147)
    ·
      refine ⟨392879193216437589181266221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261919462144291726120844147 392879193216437589181266221)
      ·
        refine ⟨147329697456164095942974833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392879193216437589181266221 147329697456164095942974833)
        ·
          refine ⟨110497273092123071957231125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147329697456164095942974833 110497273092123071957231125)
          ·
            refine ⟨5179559676193268997995209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110497273092123071957231125 5179559676193268997995209)
            ·
              refine ⟨3884669757144951748496407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5179559676193268997995209 3884669757144951748496407)
              ·
                refine ⟨5827004635717427622744611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884669757144951748496407 5827004635717427622744611)
                ·
                  refine ⟨8740506953576141434116917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827004635717427622744611 8740506953576141434116917)
                  ·
                    refine ⟨819422526897763259448461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8740506953576141434116917 819422526897763259448461)
                    ·
                      rfl

theorem cell23_4787459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 5].length) (baseStart_4787459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787459 prefixEnd_4787459 := by exact prefixLift 4787459
  have htrace : WordTrace (prefixWord ++ tailWord_4787459) baseStart_4787459 baseEnd_4787459 := by
    simpa [prefixWord, tailWord_4787459, baseEnd_4787459] using wordTrace_append hprefix tailTrace_4787459
  have hstable : (prefixWord ++ tailWord_4787459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787459).length < 2 ^ (prefixWord ++ tailWord_4787459).sum := by decide
  have hdescent : baseEnd_4787459 < baseStart_4787459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787465 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_4787465 : Nat := 118140960795 + 4787465 * 2 ^ 59
def prefixEnd_4787465 : Nat := 4983230072969 + 3 ^ 40 * 4787465 * 2
def baseEnd_4787465 : Nat := 2458270661577216754870355

theorem tailTrace_4787465 : CollatzResearch.WordTrace tailWord_4787465 prefixEnd_4787465 2458270661577216754870355 := by
  unfold tailWord_4787465
  simp only [CollatzResearch.WordTrace]
  refine ⟨174613193600839413771947849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116408795733892942514631899 174613193600839413771947849)
  ·
    refine ⟨130959895200629560328960887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174613193600839413771947849 130959895200629560328960887)
    ·
      refine ⟨196439842800944340493441331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130959895200629560328960887 196439842800944340493441331)
      ·
        refine ⟨294659764201416510740161997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196439842800944340493441331 294659764201416510740161997)
        ·
          refine ⟨110497411575531191527560749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294659764201416510740161997 110497411575531191527560749)
          ·
            refine ⟨41436529340824196822835281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110497411575531191527560749 41436529340824196822835281)
            ·
              refine ⟨31077397005618147617126461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41436529340824196822835281 31077397005618147617126461)
              ·
                refine ⟨11654023877106805356422423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31077397005618147617126461 11654023877106805356422423)
                ·
                  refine ⟨17481035815660208034633635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11654023877106805356422423 17481035815660208034633635)
                  ·
                    refine ⟨26221553723490312051950453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17481035815660208034633635 26221553723490312051950453)
                    ·
                      refine ⟨2458270661577216754870355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26221553723490312051950453 2458270661577216754870355)
                      ·
                        rfl

theorem cell23_4787465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_4787465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787465 prefixEnd_4787465 := by exact prefixLift 4787465
  have htrace : WordTrace (prefixWord ++ tailWord_4787465) baseStart_4787465 baseEnd_4787465 := by
    simpa [prefixWord, tailWord_4787465, baseEnd_4787465] using wordTrace_append hprefix tailTrace_4787465
  have hstable : (prefixWord ++ tailWord_4787465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787465).length < 2 ^ (prefixWord ++ tailWord_4787465).sum := by decide
  have hdescent : baseEnd_4787465 < baseStart_4787465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787482 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_4787482 : Nat := 118140960795 + 4787482 * 2 ^ 59
def prefixEnd_4787482 : Nat := 4983230072969 + 3 ^ 40 * 4787482 * 2
def baseEnd_4787482 : Nat := 2458279390748343188357777

theorem tailTrace_4787482 : CollatzResearch.WordTrace tailWord_4787482 prefixEnd_4787482 2458279390748343188357777 := by
  unfold tailWord_4787482
  simp only [CollatzResearch.WordTrace]
  refine ⟨43653453410444456418829175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116409209094518550450211133 43653453410444456418829175)
  ·
    refine ⟨65480180115666684628243763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43653453410444456418829175 65480180115666684628243763)
    ·
      refine ⟨98220270173500026942365645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65480180115666684628243763 98220270173500026942365645)
      ·
        refine ⟨36832601315062510103387117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98220270173500026942365645 36832601315062510103387117)
        ·
          refine ⟨13812225493148441288770169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36832601315062510103387117 13812225493148441288770169)
          ·
            refine ⟨10359169119861330966577627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13812225493148441288770169 10359169119861330966577627)
            ·
              refine ⟨15538753679791996449866441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10359169119861330966577627 15538753679791996449866441)
              ·
                refine ⟨11654065259843997337399831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15538753679791996449866441 11654065259843997337399831)
                ·
                  refine ⟨17481097889765996006099747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11654065259843997337399831 17481097889765996006099747)
                  ·
                    refine ⟨26221646834648994009149621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17481097889765996006099747 26221646834648994009149621)
                    ·
                      refine ⟨2458279390748343188357777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26221646834648994009149621 2458279390748343188357777)
                      ·
                        rfl

theorem cell23_4787482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_4787482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787482 prefixEnd_4787482 := by exact prefixLift 4787482
  have htrace : WordTrace (prefixWord ++ tailWord_4787482) baseStart_4787482 baseEnd_4787482 := by
    simpa [prefixWord, tailWord_4787482, baseEnd_4787482] using wordTrace_append hprefix tailTrace_4787482
  have hstable : (prefixWord ++ tailWord_4787482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787482).length < 2 ^ (prefixWord ++ tailWord_4787482).sum := by decide
  have hdescent : baseEnd_4787482 < baseStart_4787482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787496 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_4787496 : Nat := 118140960795 + 4787496 * 2 ^ 59
def prefixEnd_4787496 : Nat := 4983230072969 + 3 ^ 40 * 4787496 * 2
def baseEnd_4787496 : Nat := 2458286579477506133582713

theorem tailTrace_4787496 : CollatzResearch.WordTrace tailWord_4787496 prefixEnd_4787496 2458286579477506133582713 := by
  unfold tailWord_4787496
  simp only [CollatzResearch.WordTrace]
  refine ⟨87307162131863553033163171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116409549509151404044217561 87307162131863553033163171)
  ·
    refine ⟨130960743197795329549744757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87307162131863553033163171 130960743197795329549744757)
    ·
      refine ⟨12277569674793312145288571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130960743197795329549744757 12277569674793312145288571)
      ·
        refine ⟨18416354512189968217932857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12277569674793312145288571 18416354512189968217932857)
        ·
          refine ⟨13812265884142476163449643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18416354512189968217932857 13812265884142476163449643)
          ·
            refine ⟨20718398826213714245174465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13812265884142476163449643 20718398826213714245174465)
            ·
              refine ⟨15538799119660285683880849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20718398826213714245174465 15538799119660285683880849)
              ·
                refine ⟨11654099339745214262910637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15538799119660285683880849 11654099339745214262910637)
                ·
                  refine ⟨4370287252404455348591489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11654099339745214262910637 4370287252404455348591489)
                  ·
                    refine ⟨3277715439303341511443617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4370287252404455348591489 3277715439303341511443617)
                    ·
                      refine ⟨2458286579477506133582713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277715439303341511443617 2458286579477506133582713)
                      ·
                        rfl

theorem cell23_4787496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_4787496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787496 prefixEnd_4787496 := by exact prefixLift 4787496
  have htrace : WordTrace (prefixWord ++ tailWord_4787496) baseStart_4787496 baseEnd_4787496 := by
    simpa [prefixWord, tailWord_4787496, baseEnd_4787496] using wordTrace_append hprefix tailTrace_4787496
  have hstable : (prefixWord ++ tailWord_4787496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787496).length < 2 ^ (prefixWord ++ tailWord_4787496).sum := by decide
  have hdescent : baseEnd_4787496 < baseStart_4787496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787545 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 2, 6]
def baseStart_4787545 : Nat := 118140960795 + 4787545 * 2 ^ 59
def prefixEnd_4787545 : Nat := 4983230072969 + 3 ^ 40 * 4787545 * 2
def baseEnd_4787545 : Nat := 819437246676525480623329

theorem tailTrace_4787545 : CollatzResearch.WordTrace tailWord_4787545 prefixEnd_4787545 819437246676525480623329 := by
  unfold tailWord_4787545
  simp only [CollatzResearch.WordTrace]
  refine ⟨174616111440549587434860089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116410740960366391623240059 174616111440549587434860089)
  ·
    refine ⟨130962083580412190576145067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174616111440549587434860089 130962083580412190576145067)
    ·
      refine ⟨196443125370618285864217601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130962083580412190576145067 196443125370618285864217601)
      ·
        refine ⟨147332344027963714398163201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196443125370618285864217601 147332344027963714398163201)
        ·
          refine ⟨110499258020972785798622401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147332344027963714398163201 110499258020972785798622401)
          ·
            refine ⟨82874443515729589348966801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110499258020972785798622401 82874443515729589348966801)
            ·
              refine ⟨62155832636797192011725101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82874443515729589348966801 62155832636797192011725101)
              ·
                refine ⟨23308437238798947004396913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62155832636797192011725101 23308437238798947004396913)
                ·
                  refine ⟨17481327929099210253297685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23308437238798947004396913 17481327929099210253297685)
                  ·
                    refine ⟨819437246676525480623329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17481327929099210253297685 819437246676525480623329)
                    ·
                      rfl

theorem cell23_4787545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_4787545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787545 prefixEnd_4787545 := by exact prefixLift 4787545
  have htrace : WordTrace (prefixWord ++ tailWord_4787545) baseStart_4787545 baseEnd_4787545 := by
    simpa [prefixWord, tailWord_4787545, baseEnd_4787545] using wordTrace_append hprefix tailTrace_4787545
  have hstable : (prefixWord ++ tailWord_4787545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787545).length < 2 ^ (prefixWord ++ tailWord_4787545).sum := by decide
  have hdescent : baseEnd_4787545 < baseStart_4787545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787546 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3]
def baseStart_4787546 : Nat := 118140960795 + 4787546 * 2 ^ 59
def prefixEnd_4787546 : Nat := 4983230072969 + 3 ^ 40 * 4787546 * 2
def baseEnd_4787546 : Nat := 2458312253510230937957483

theorem tailTrace_4787546 : CollatzResearch.WordTrace tailWord_4787546 prefixEnd_4787546 2458312253510230937957483 := by
  unfold tailWord_4787546
  simp only [CollatzResearch.WordTrace]
  refine ⟨43654036978386491151411623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116410765275697309737097661 43654036978386491151411623)
  ·
    refine ⟨65481055467579736727117435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43654036978386491151411623 65481055467579736727117435)
    ·
      refine ⟨98221583201369605090676153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65481055467579736727117435 98221583201369605090676153)
      ·
        refine ⟨73666187401027203818007115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98221583201369605090676153 73666187401027203818007115)
        ·
          refine ⟨110499281101540805727010673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73666187401027203818007115 110499281101540805727010673)
          ·
            refine ⟨82874460826155604295258005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110499281101540805727010673 82874460826155604295258005)
            ·
              refine ⟨3884740351226043951340219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82874460826155604295258005 3884740351226043951340219)
              ·
                refine ⟨5827110526839065927010329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884740351226043951340219 5827110526839065927010329)
                ·
                  refine ⟨4370332895129299445257747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5827110526839065927010329 4370332895129299445257747)
                  ·
                    refine ⟨6555499342693949167886621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4370332895129299445257747 6555499342693949167886621)
                    ·
                      refine ⟨2458312253510230937957483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6555499342693949167886621 2458312253510230937957483)
                      ·
                        rfl

theorem cell23_4787546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_4787546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787546 prefixEnd_4787546 := by exact prefixLift 4787546
  have htrace : WordTrace (prefixWord ++ tailWord_4787546) baseStart_4787546 baseEnd_4787546 := by
    simpa [prefixWord, tailWord_4787546, baseEnd_4787546] using wordTrace_append hprefix tailTrace_4787546
  have hstable : (prefixWord ++ tailWord_4787546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787546).length < 2 ^ (prefixWord ++ tailWord_4787546).sum := by decide
  have hdescent : baseEnd_4787546 < baseStart_4787546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787556 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_4787556 : Nat := 118140960795 + 4787556 * 2 ^ 59
def prefixEnd_4787556 : Nat := 4983230072969 + 3 ^ 40 * 4787556 * 2
def baseEnd_4787556 : Nat := 2458317388316775898832437

theorem tailTrace_4787556 : CollatzResearch.WordTrace tailWord_4787556 prefixEnd_4787556 2458317388316775898832437 := by
  unfold tailWord_4787556
  simp only [CollatzResearch.WordTrace]
  refine ⟨87308256321754868156755261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116411008429006490875673681 87308256321754868156755261)
  ·
    refine ⟨32740596120658075558783223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87308256321754868156755261 32740596120658075558783223)
    ·
      refine ⟨49110894180987113338174835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32740596120658075558783223 49110894180987113338174835)
      ·
        refine ⟨73666341271480670007262253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49110894180987113338174835 73666341271480670007262253)
        ·
          refine ⟨27624877976805251252723345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73666341271480670007262253 27624877976805251252723345)
          ·
            refine ⟨20718658482603938439542509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27624877976805251252723345 20718658482603938439542509)
            ·
              refine ⟨7769496930976476914828441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20718658482603938439542509 7769496930976476914828441)
              ·
                refine ⟨5827122698232357686121331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7769496930976476914828441 5827122698232357686121331)
                ·
                  refine ⟨8740684047348536529181997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827122698232357686121331 8740684047348536529181997)
                  ·
                    refine ⟨3277756517755701198443249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8740684047348536529181997 3277756517755701198443249)
                    ·
                      refine ⟨2458317388316775898832437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277756517755701198443249 2458317388316775898832437)
                      ·
                        rfl

theorem cell23_4787556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_4787556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787556 prefixEnd_4787556 := by exact prefixLift 4787556
  have htrace : WordTrace (prefixWord ++ tailWord_4787556) baseStart_4787556 baseEnd_4787556 := by
    simpa [prefixWord, tailWord_4787556, baseEnd_4787556] using wordTrace_append hprefix tailTrace_4787556
  have hstable : (prefixWord ++ tailWord_4787556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787556).length < 2 ^ (prefixWord ++ tailWord_4787556).sum := by decide
  have hdescent : baseEnd_4787556 < baseStart_4787556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787569 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 6, 2, 2]
def baseStart_4787569 : Nat := 118140960795 + 4787569 * 2 ^ 59
def prefixEnd_4787569 : Nat := 4983230072969 + 3 ^ 40 * 4787569 * 2
def baseEnd_4787569 : Nat := 2458324063565284347969877

theorem tailTrace_4787569 : CollatzResearch.WordTrace tailWord_4787569 prefixEnd_4787569 2458324063565284347969877 := by
  unfold tailWord_4787569
  simp only [CollatzResearch.WordTrace]
  refine ⟨174616986792462639533733761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116411324528308426355822507 174616986792462639533733761)
  ·
    refine ⟨130962740094346979650300321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174616986792462639533733761 130962740094346979650300321)
    ·
      refine ⟨98222055070760234737725241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130962740094346979650300321 98222055070760234737725241)
      ·
        refine ⟨73666541303070176053293931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98222055070760234737725241 73666541303070176053293931)
        ·
          refine ⟨110499811954605264079940897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73666541303070176053293931 110499811954605264079940897)
          ·
            refine ⟨82874858965953948059955673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110499811954605264079940897 82874858965953948059955673)
            ·
              refine ⟨62156144224465461044966755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82874858965953948059955673 62156144224465461044966755)
              ·
                refine ⟨93234216336698191567450133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62156144224465461044966755 93234216336698191567450133)
                ·
                  refine ⟨4370353890782727729724225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93234216336698191567450133 4370353890782727729724225)
                  ·
                    refine ⟨3277765418087045797293169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4370353890782727729724225 3277765418087045797293169)
                    ·
                      refine ⟨2458324063565284347969877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277765418087045797293169 2458324063565284347969877)
                      ·
                        rfl

theorem cell23_4787569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_4787569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787569 prefixEnd_4787569 := by exact prefixLift 4787569
  have htrace : WordTrace (prefixWord ++ tailWord_4787569) baseStart_4787569 baseEnd_4787569 := by
    simpa [prefixWord, tailWord_4787569, baseEnd_4787569] using wordTrace_append hprefix tailTrace_4787569
  have hstable : (prefixWord ++ tailWord_4787569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787569).length < 2 ^ (prefixWord ++ tailWord_4787569).sum := by decide
  have hdescent : baseEnd_4787569 < baseStart_4787569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787635 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 10]
def baseStart_4787635 : Nat := 118140960795 + 4787635 * 2 ^ 59
def prefixEnd_4787635 : Nat := 4983230072969 + 3 ^ 40 * 4787635 * 2
def baseEnd_4787635 : Nat := 819452651096160363248191

theorem tailTrace_4787635 : CollatzResearch.WordTrace tailWord_4787635 prefixEnd_4787635 819452651096160363248191 := by
  unfold tailWord_4787635
  simp only [CollatzResearch.WordTrace]
  refine ⟨174619394010223532805636359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116412929340149021870424239 174619394010223532805636359)
  ·
    refine ⟨261929091015335299208454539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174619394010223532805636359 261929091015335299208454539)
    ·
      refine ⟨392893636523002948812681809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261929091015335299208454539 392893636523002948812681809)
      ·
        refine ⟨294670227392252211609511357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392893636523002948812681809 294670227392252211609511357)
        ·
          refine ⟨110501335272094579353566759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294670227392252211609511357 110501335272094579353566759)
          ·
            refine ⟨165752002908141869030350139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110501335272094579353566759 165752002908141869030350139)
            ·
              refine ⟨248628004362212803545525209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165752002908141869030350139 248628004362212803545525209)
              ·
                refine ⟨186471003271659602659143907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248628004362212803545525209 186471003271659602659143907)
                ·
                  refine ⟨279706504907489403988715861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186471003271659602659143907 279706504907489403988715861)
                  ·
                    refine ⟨819452651096160363248191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 279706504907489403988715861 819452651096160363248191)
                    ·
                      rfl

theorem cell23_4787635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 10].length) (baseStart_4787635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787635 prefixEnd_4787635 := by exact prefixLift 4787635
  have htrace : WordTrace (prefixWord ++ tailWord_4787635) baseStart_4787635 baseEnd_4787635 := by
    simpa [prefixWord, tailWord_4787635, baseEnd_4787635] using wordTrace_append hprefix tailTrace_4787635
  have hstable : (prefixWord ++ tailWord_4787635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787635).length < 2 ^ (prefixWord ++ tailWord_4787635).sum := by decide
  have hdescent : baseEnd_4787635 < baseStart_4787635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787659 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 2, 4, 2]
def baseStart_4787659 : Nat := 118140960795 + 4787659 * 2 ^ 59
def prefixEnd_4787659 : Nat := 4983230072969 + 3 ^ 40 * 4787659 * 2
def baseEnd_4787659 : Nat := 2458370276824188995844463

theorem tailTrace_4787659 : CollatzResearch.WordTrace tailWord_4787659 prefixEnd_4787659 2458370276824188995844463 := by
  unfold tailWord_4787659
  simp only [CollatzResearch.WordTrace]
  refine ⟨174620269362136584904510031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116413512908091056603006687 174620269362136584904510031)
  ·
    refine ⟨261930404043204877356765047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174620269362136584904510031 261930404043204877356765047)
    ·
      refine ⟨392895606064807316035147571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261930404043204877356765047 392895606064807316035147571)
      ·
        refine ⟨589343409097210974052721357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392895606064807316035147571 589343409097210974052721357)
        ·
          refine ⟨221003778411454115269770509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 589343409097210974052721357 221003778411454115269770509)
          ·
            refine ⟨82876416904295293226163941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221003778411454115269770509 82876416904295293226163941)
            ·
              refine ⟨15539328169555367479905739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82876416904295293226163941 15539328169555367479905739)
              ·
                refine ⟨23308992254333051219858609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15539328169555367479905739 23308992254333051219858609)
                ·
                  refine ⟨17481744190749788414893957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23308992254333051219858609 17481744190749788414893957)
                  ·
                    refine ⟨3277827035765585327792617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17481744190749788414893957 3277827035765585327792617)
                    ·
                      refine ⟨2458370276824188995844463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277827035765585327792617 2458370276824188995844463)
                      ·
                        rfl

theorem cell23_4787659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4, 2].length) (baseStart_4787659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787659 prefixEnd_4787659 := by exact prefixLift 4787659
  have htrace : WordTrace (prefixWord ++ tailWord_4787659) baseStart_4787659 baseEnd_4787659 := by
    simpa [prefixWord, tailWord_4787659, baseEnd_4787659] using wordTrace_append hprefix tailTrace_4787659
  have hstable : (prefixWord ++ tailWord_4787659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787659).length < 2 ^ (prefixWord ++ tailWord_4787659).sum := by decide
  have hdescent : baseEnd_4787659 < baseStart_4787659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787669 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_4787669 : Nat := 118140960795 + 4787669 * 2 ^ 59
def prefixEnd_4787669 : Nat := 4983230072969 + 3 ^ 40 * 4787669 * 2
def baseEnd_4787669 : Nat := 819458470543577985573139

theorem tailTrace_4787669 : CollatzResearch.WordTrace tailWord_4787669 prefixEnd_4787669 819458470543577985573139 := by
  unfold tailWord_4787669
  simp only [CollatzResearch.WordTrace]
  refine ⟨174620634092100356612374061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116413756061400237741582707 174620634092100356612374061)
  ·
    refine ⟨65482737784537633729640273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174620634092100356612374061 65482737784537633729640273)
    ·
      refine ⟨49112053338403225297230205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65482737784537633729640273 49112053338403225297230205)
      ·
        refine ⟨18417020001901209486461327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49112053338403225297230205 18417020001901209486461327)
        ·
          refine ⟨27625530002851814229691991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18417020001901209486461327 27625530002851814229691991)
          ·
            refine ⟨41438295004277721344537987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27625530002851814229691991 41438295004277721344537987)
            ·
              refine ⟨62157442506416582016806981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41438295004277721344537987 62157442506416582016806981)
              ·
                refine ⟨11654520469953109128151309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62157442506416582016806981 11654520469953109128151309)
                ·
                  refine ⟨4370445176232415923056741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11654520469953109128151309 4370445176232415923056741)
                  ·
                    refine ⟨819458470543577985573139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4370445176232415923056741 819458470543577985573139)
                    ·
                      rfl

theorem cell23_4787669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_4787669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787669 prefixEnd_4787669 := by exact prefixLift 4787669
  have htrace : WordTrace (prefixWord ++ tailWord_4787669) baseStart_4787669 baseEnd_4787669 := by
    simpa [prefixWord, tailWord_4787669, baseEnd_4787669] using wordTrace_append hprefix tailTrace_4787669
  have hstable : (prefixWord ++ tailWord_4787669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787669).length < 2 ^ (prefixWord ++ tailWord_4787669).sum := by decide
  have hdescent : baseEnd_4787669 < baseStart_4787669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787679 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 3]
def baseStart_4787679 : Nat := 118140960795 + 4787679 * 2 ^ 59
def prefixEnd_4787679 : Nat := 4983230072969 + 3 ^ 40 * 4787679 * 2
def baseEnd_4787679 : Nat := 2458380546437278917594371

theorem tailTrace_4787679 : CollatzResearch.WordTrace tailWord_4787679 prefixEnd_4787679 2458380546437278917594371 := by
  unfold tailWord_4787679
  simp only [CollatzResearch.WordTrace]
  refine ⟨174620998822064128320238091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116413999214709418880158727 174620998822064128320238091)
  ·
    refine ⟨261931498233096192480357137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174620998822064128320238091 261931498233096192480357137)
    ·
      refine ⟨196448623674822144360267853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261931498233096192480357137 196448623674822144360267853)
      ·
        refine ⟨73668233878058304135100445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196448623674822144360267853 73668233878058304135100445)
        ·
          refine ⟨27625587704271864050662667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73668233878058304135100445 27625587704271864050662667)
          ·
            refine ⟨41438381556407796075994001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27625587704271864050662667 41438381556407796075994001)
            ·
              refine ⟨31078786167305847056995501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41438381556407796075994001 31078786167305847056995501)
              ·
                refine ⟨11654544812739692646373313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31078786167305847056995501 11654544812739692646373313)
                ·
                  refine ⟨8740908609554769484779985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11654544812739692646373313 8740908609554769484779985)
                  ·
                    refine ⟨6555681457166077113584989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8740908609554769484779985 6555681457166077113584989)
                    ·
                      refine ⟨2458380546437278917594371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6555681457166077113584989 2458380546437278917594371)
                      ·
                        rfl

theorem cell23_4787679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_4787679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787679 prefixEnd_4787679 := by exact prefixLift 4787679
  have htrace : WordTrace (prefixWord ++ tailWord_4787679) baseStart_4787679 baseEnd_4787679 := by
    simpa [prefixWord, tailWord_4787679, baseEnd_4787679] using wordTrace_append hprefix tailTrace_4787679
  have hstable : (prefixWord ++ tailWord_4787679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787679).length < 2 ^ (prefixWord ++ tailWord_4787679).sum := by decide
  have hdescent : baseEnd_4787679 < baseStart_4787679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787716 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 6]
def baseStart_4787716 : Nat := 118140960795 + 4787716 * 2 ^ 59
def prefixEnd_4787716 : Nat := 4983230072969 + 3 ^ 40 * 4787716 * 2
def baseEnd_4787716 : Nat := 273155505024610585870189

theorem tailTrace_4787716 : CollatzResearch.WordTrace tailWord_4787716 prefixEnd_4787716 273155505024610585870189 := by
  unfold tailWord_4787716
  simp only [CollatzResearch.WordTrace]
  refine ⟨87311174161465041819667501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116414898881953389092890001 87311174161465041819667501)
  ·
    refine ⟨32741690310549390682375313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87311174161465041819667501 32741690310549390682375313)
    ·
      refine ⟨24556267732912043011781485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32741690310549390682375313 24556267732912043011781485)
      ·
        refine ⟨9208600399842016129418057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24556267732912043011781485 9208600399842016129418057)
        ·
          refine ⟨6906450299881512097063543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9208600399842016129418057 6906450299881512097063543)
          ·
            refine ⟨10359675449822268145595315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6906450299881512097063543 10359675449822268145595315)
            ·
              refine ⟨15539513174733402218392973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10359675449822268145595315 15539513174733402218392973)
              ·
                refine ⟨5827317440525025831897365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15539513174733402218392973 5827317440525025831897365)
                ·
                  refine ⟨273155505024610585870189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5827317440525025831897365 273155505024610585870189)
                  ·
                    rfl

theorem cell23_4787716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_4787716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787716 prefixEnd_4787716 := by exact prefixLift 4787716
  have htrace : WordTrace (prefixWord ++ tailWord_4787716) baseStart_4787716 baseEnd_4787716 := by
    simpa [prefixWord, tailWord_4787716, baseEnd_4787716] using wordTrace_append hprefix tailTrace_4787716
  have hstable : (prefixWord ++ tailWord_4787716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787716).length < 2 ^ (prefixWord ++ tailWord_4787716).sum := by decide
  have hdescent : baseEnd_4787716 < baseStart_4787716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787786 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_4787786 : Nat := 118140960795 + 4787786 * 2 ^ 59
def prefixEnd_4787786 : Nat := 4983230072969 + 3 ^ 40 * 4787786 * 2
def baseEnd_4787786 : Nat := 2458435488867309998956379

theorem tailTrace_4787786 : CollatzResearch.WordTrace tailWord_4787786 prefixEnd_4787786 2458435488867309998956379 := by
  unfold tailWord_4787786
  simp only [CollatzResearch.WordTrace]
  refine ⟨43656225358169121398595803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116416600955117657062922141 43656225358169121398595803)
  ·
    refine ⟨65484338037253682097893705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43656225358169121398595803 65484338037253682097893705)
    ·
      refine ⟨49113253527940261573420279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65484338037253682097893705 49113253527940261573420279)
      ·
        refine ⟨73669880291910392360130419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49113253527940261573420279 73669880291910392360130419)
        ·
          refine ⟨110504820437865588540195629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73669880291910392360130419 110504820437865588540195629)
          ·
            refine ⟨41439307664199595702573361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110504820437865588540195629 41439307664199595702573361)
            ·
              refine ⟨31079480748149696776930021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41439307664199595702573361 31079480748149696776930021)
              ·
                refine ⟨5827402640278068145674379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31079480748149696776930021 5827402640278068145674379)
                ·
                  refine ⟨8741103960417102218511569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827402640278068145674379 8741103960417102218511569)
                  ·
                    refine ⟨6555827970312826663883677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8741103960417102218511569 6555827970312826663883677)
                    ·
                      refine ⟨2458435488867309998956379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6555827970312826663883677 2458435488867309998956379)
                      ·
                        rfl

theorem cell23_4787786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_4787786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787786 prefixEnd_4787786 := by exact prefixLift 4787786
  have htrace : WordTrace (prefixWord ++ tailWord_4787786) baseStart_4787786 baseEnd_4787786 := by
    simpa [prefixWord, tailWord_4787786, baseEnd_4787786] using wordTrace_append hprefix tailTrace_4787786
  have hstable : (prefixWord ++ tailWord_4787786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787786).length < 2 ^ (prefixWord ++ tailWord_4787786).sum := by decide
  have hdescent : baseEnd_4787786 < baseStart_4787786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787856 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 1, 4, 2]
def baseStart_4787856 : Nat := 118140960795 + 4787856 * 2 ^ 59
def prefixEnd_4787856 : Nat := 4983230072969 + 3 ^ 40 * 4787856 * 2
def baseEnd_4787856 : Nat := 2458471432513124725081057

theorem tailTrace_4787856 : CollatzResearch.WordTrace tailWord_4787856 prefixEnd_4787856 2458471432513124725081057 := by
  unfold tailWord_4787856
  simp only [CollatzResearch.WordTrace]
  refine ⟨87313727271211443774715711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116418303028281925032954281 87313727271211443774715711)
  ·
    refine ⟨130970590906817165662073567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87313727271211443774715711 130970590906817165662073567)
    ·
      refine ⟨196455886360225748493110351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130970590906817165662073567 196455886360225748493110351)
      ·
        refine ⟨294683829540338622739665527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196455886360225748493110351 294683829540338622739665527)
        ·
          refine ⟨442025744310507934109498291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294683829540338622739665527 442025744310507934109498291)
          ·
            refine ⟨663038616465761901164247437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442025744310507934109498291 663038616465761901164247437)
            ·
              refine ⟨248639481174660712936592789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663038616465761901164247437 248639481174660712936592789)
              ·
                refine ⟨11654975680062220918902787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248639481174660712936592789 11654975680062220918902787)
                ·
                  refine ⟨17482463520093331378354181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11654975680062220918902787 17482463520093331378354181)
                  ·
                    refine ⟨3277961910017499633441409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17482463520093331378354181 3277961910017499633441409)
                    ·
                      refine ⟨2458471432513124725081057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277961910017499633441409 2458471432513124725081057)
                      ·
                        rfl

theorem cell23_4787856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 4, 2].length) (baseStart_4787856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787856 prefixEnd_4787856 := by exact prefixLift 4787856
  have htrace : WordTrace (prefixWord ++ tailWord_4787856) baseStart_4787856 baseEnd_4787856 := by
    simpa [prefixWord, tailWord_4787856, baseEnd_4787856] using wordTrace_append hprefix tailTrace_4787856
  have hstable : (prefixWord ++ tailWord_4787856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787856).length < 2 ^ (prefixWord ++ tailWord_4787856).sum := by decide
  have hdescent : baseEnd_4787856 < baseStart_4787856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787894 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_4787894 : Nat := 118140960795 + 4787894 * 2 ^ 59
def prefixEnd_4787894 : Nat := 4983230072969 + 3 ^ 40 * 4787894 * 2
def baseEnd_4787894 : Nat := 2458490944777995576405883

theorem tailTrace_4787894 : CollatzResearch.WordTrace tailWord_4787894 prefixEnd_4787894 2458490944777995576405883 := by
  unfold tailWord_4787894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10914302532267826252457171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116419227010856813359543157 10914302532267826252457171)
  ·
    refine ⟨16371453798401739378685757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10914302532267826252457171 16371453798401739378685757)
    ·
      refine ⟨6139295174400652267007159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16371453798401739378685757 6139295174400652267007159)
      ·
        refine ⟨9208942761600978400510739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139295174400652267007159 9208942761600978400510739)
        ·
          refine ⟨13813414142401467600766109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9208942761600978400510739 13813414142401467600766109)
          ·
            refine ⟨5180030303400550350287291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13813414142401467600766109 5180030303400550350287291)
            ·
              refine ⟨7770045455100825525430937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180030303400550350287291 7770045455100825525430937)
              ·
                refine ⟨5827534091325619144073203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7770045455100825525430937 5827534091325619144073203)
                ·
                  refine ⟨8741301136988428716109805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827534091325619144073203 8741301136988428716109805)
                  ·
                    refine ⟨3277987926370660768541177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8741301136988428716109805 3277987926370660768541177)
                    ·
                      refine ⟨2458490944777995576405883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3277987926370660768541177 2458490944777995576405883)
                      ·
                        rfl

theorem cell23_4787894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_4787894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787894 prefixEnd_4787894 := by exact prefixLift 4787894
  have htrace : WordTrace (prefixWord ++ tailWord_4787894) baseStart_4787894 baseEnd_4787894 := by
    simpa [prefixWord, tailWord_4787894, baseEnd_4787894] using wordTrace_append hprefix tailTrace_4787894
  have hstable : (prefixWord ++ tailWord_4787894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787894).length < 2 ^ (prefixWord ++ tailWord_4787894).sum := by decide
  have hdescent : baseEnd_4787894 < baseStart_4787894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787909 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_4787909 : Nat := 118140960795 + 4787909 * 2 ^ 59
def prefixEnd_4787909 : Nat := 4983230072969 + 3 ^ 40 * 4787909 * 2
def baseEnd_4787909 : Nat := 819499548995937672572771

theorem tailTrace_4787909 : CollatzResearch.WordTrace tailWord_4787909 prefixEnd_4787909 819499548995937672572771 := by
  unfold tailWord_4787909
  simp only [CollatzResearch.WordTrace]
  refine ⟨174629387611230877601110781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116419591740820585067407187 174629387611230877601110781)
  ·
    refine ⟨65486020354211579100416543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174629387611230877601110781 65486020354211579100416543)
    ·
      refine ⟨98229030531317368650624815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65486020354211579100416543 98229030531317368650624815)
      ·
        refine ⟨147343545796976052975937223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98229030531317368650624815 147343545796976052975937223)
        ·
          refine ⟨221015318695464079463905835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147343545796976052975937223 221015318695464079463905835)
          ·
            refine ⟨331522978043196119195858753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221015318695464079463905835 331522978043196119195858753)
            ·
              refine ⟨248642233532397089396894065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331522978043196119195858753 248642233532397089396894065)
              ·
                refine ⟨186481675149297817047670549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248642233532397089396894065 186481675149297817047670549)
                ·
                  refine ⟨8741328522623335174109557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 186481675149297817047670549 8741328522623335174109557)
                  ·
                    refine ⟨819499548995937672572771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8741328522623335174109557 819499548995937672572771)
                    ·
                      rfl

theorem cell23_4787909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_4787909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787909 prefixEnd_4787909 := by exact prefixLift 4787909
  have htrace : WordTrace (prefixWord ++ tailWord_4787909) baseStart_4787909 baseEnd_4787909 := by
    simpa [prefixWord, tailWord_4787909, baseEnd_4787909] using wordTrace_append hprefix tailTrace_4787909
  have hstable : (prefixWord ++ tailWord_4787909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787909).length < 2 ^ (prefixWord ++ tailWord_4787909).sum := by decide
  have hdescent : baseEnd_4787909 < baseStart_4787909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787910 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4787910 : Nat := 118140960795 + 4787910 * 2 ^ 59
def prefixEnd_4787910 : Nat := 4983230072969 + 3 ^ 40 * 4787910 * 2
def baseEnd_4787910 : Nat := 2458499160468467513805809

theorem tailTrace_4787910 : CollatzResearch.WordTrace tailWord_4787910 prefixEnd_4787910 2458499160468467513805809 := by
  unfold tailWord_4787910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457169502632101711621787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116419616056151503181264789 5457169502632101711621787)
  ·
    refine ⟨8185754253948152567432681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5457169502632101711621787 8185754253948152567432681)
    ·
      refine ⟨6139315690461114425574511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8185754253948152567432681 6139315690461114425574511)
      ·
        refine ⟨9208973535691671638361767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139315690461114425574511 9208973535691671638361767)
        ·
          refine ⟨13813460303537507457542651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9208973535691671638361767 13813460303537507457542651)
          ·
            refine ⟨20720190455306261186313977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13813460303537507457542651 20720190455306261186313977)
            ·
              refine ⟨15540142841479695889735483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20720190455306261186313977 15540142841479695889735483)
              ·
                refine ⟨23310214262219543834603225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15540142841479695889735483 23310214262219543834603225)
                ·
                  refine ⟨17482660696664657875952419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23310214262219543834603225 17482660696664657875952419)
                  ·
                    refine ⟨26223991044996986813928629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17482660696664657875952419 26223991044996986813928629)
                    ·
                      refine ⟨2458499160468467513805809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26223991044996986813928629 2458499160468467513805809)
                      ·
                        rfl

theorem cell23_4787910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4787910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787910 prefixEnd_4787910 := by exact prefixLift 4787910
  have htrace : WordTrace (prefixWord ++ tailWord_4787910) baseStart_4787910 baseEnd_4787910 := by
    simpa [prefixWord, tailWord_4787910, baseEnd_4787910] using wordTrace_append hprefix tailTrace_4787910
  have hstable : (prefixWord ++ tailWord_4787910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787910).length < 2 ^ (prefixWord ++ tailWord_4787910).sum := by decide
  have hdescent : baseEnd_4787910 < baseStart_4787910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787930 : List Nat := [3, 1, 1, 2, 2, 5, 2, 2, 5]
def baseStart_4787930 : Nat := 118140960795 + 4787930 * 2 ^ 59
def prefixEnd_4787930 : Nat := 4983230072969 + 3 ^ 40 * 4787930 * 2
def baseEnd_4787930 : Nat := 273167714453506381728413

theorem tailTrace_4787930 : CollatzResearch.WordTrace tailWord_4787930 prefixEnd_4787930 273167714453506381728413 := by
  unfold tailWord_4787930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43657538386038699546906311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116420102362769865458416829 43657538386038699546906311)
  ·
    refine ⟨65486307579058049320359467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43657538386038699546906311 65486307579058049320359467)
    ·
      refine ⟨98229461368587073980539201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65486307579058049320359467 98229461368587073980539201)
      ·
        refine ⟨73672096026440305485404401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98229461368587073980539201 73672096026440305485404401)
        ·
          refine ⟨55254072019830229114053301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73672096026440305485404401 55254072019830229114053301)
          ·
            refine ⟨5180069251859083979442497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55254072019830229114053301 5180069251859083979442497)
            ·
              refine ⟨3885051938894312984581873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5180069251859083979442497 3885051938894312984581873)
              ·
                refine ⟨2913788954170734738436405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3885051938894312984581873 2913788954170734738436405)
                ·
                  refine ⟨273167714453506381728413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2913788954170734738436405 273167714453506381728413)
                  ·
                    rfl

theorem cell23_4787930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_4787930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787930 prefixEnd_4787930 := by exact prefixLift 4787930
  have htrace : WordTrace (prefixWord ++ tailWord_4787930) baseStart_4787930 baseEnd_4787930 := by
    simpa [prefixWord, tailWord_4787930, baseEnd_4787930] using wordTrace_append hprefix tailTrace_4787930
  have hstable : (prefixWord ++ tailWord_4787930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787930).length < 2 ^ (prefixWord ++ tailWord_4787930).sum := by decide
  have hdescent : baseEnd_4787930 < baseStart_4787930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787946 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_4787946 : Nat := 118140960795 + 4787946 * 2 ^ 59
def prefixEnd_4787946 : Nat := 4983230072969 + 3 ^ 40 * 4787946 * 2
def baseEnd_4787946 : Nat := 2458517645772029372955643

theorem tailTrace_4787946 : CollatzResearch.WordTrace tailWord_4787946 prefixEnd_4787946 2458517645772029372955643 := by
  unfold tailWord_4787946
  simp only [CollatzResearch.WordTrace]
  refine ⟨43657684278024208230051923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116420491408064555280138461 43657684278024208230051923)
  ·
    refine ⟨65486526417036312345077885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43657684278024208230051923 65486526417036312345077885)
    ·
      refine ⟨24557447406388617129404207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65486526417036312345077885 24557447406388617129404207)
      ·
        refine ⟨36836171109582925694106311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24557447406388617129404207 36836171109582925694106311)
        ·
          refine ⟨55254256664374388541159467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36836171109582925694106311 55254256664374388541159467)
          ·
            refine ⟨82881384996561582811739201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55254256664374388541159467 82881384996561582811739201)
            ·
              refine ⟨62161038747421187108804401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82881384996561582811739201 62161038747421187108804401)
              ·
                refine ⟨46620779060565890331603301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62161038747421187108804401 46620779060565890331603301)
                ·
                  refine ⟨8741396073856104437175619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46620779060565890331603301 8741396073856104437175619)
                  ·
                    refine ⟨13112094110784156655763429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8741396073856104437175619 13112094110784156655763429)
                    ·
                      refine ⟨2458517645772029372955643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13112094110784156655763429 2458517645772029372955643)
                      ·
                        rfl

theorem cell23_4787946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_4787946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787946 prefixEnd_4787946 := by exact prefixLift 4787946
  have htrace : WordTrace (prefixWord ++ tailWord_4787946) baseStart_4787946 baseEnd_4787946 := by
    simpa [prefixWord, tailWord_4787946, baseEnd_4787946] using wordTrace_append hprefix tailTrace_4787946
  have hstable : (prefixWord ++ tailWord_4787946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787946).length < 2 ^ (prefixWord ++ tailWord_4787946).sum := by decide
  have hdescent : baseEnd_4787946 < baseStart_4787946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788040 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_4788040 : Nat := 118140960795 + 4788040 * 2 ^ 59
def prefixEnd_4788040 : Nat := 4983230072969 + 3 ^ 40 * 4788040 * 2
def baseEnd_4788040 : Nat := 2458565912953552005180211

theorem tailTrace_4788040 : CollatzResearch.WordTrace tailWord_4788040 prefixEnd_4788040 2458565912953552005180211 := by
  unfold tailWord_4788040
  simp only [CollatzResearch.WordTrace]
  refine ⟨87317082786878143487064787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116422777049170857982753049 87317082786878143487064787)
  ·
    refine ⟨130975624180317215230597181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87317082786878143487064787 130975624180317215230597181)
    ·
      refine ⟨49115859067618955711473943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130975624180317215230597181 49115859067618955711473943)
      ·
        refine ⟨73673788601428433567210915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49115859067618955711473943 73673788601428433567210915)
        ·
          refine ⟨110510682902142650350816373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73673788601428433567210915 110510682902142650350816373)
          ·
            refine ⟨10360376522075873470389035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110510682902142650350816373 10360376522075873470389035)
            ·
              refine ⟨15540564783113810205583553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10360376522075873470389035 15540564783113810205583553)
              ·
                refine ⟨11655423587335357654187665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15540564783113810205583553 11655423587335357654187665)
                ·
                  refine ⟨8741567690501518240640749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11655423587335357654187665 8741567690501518240640749)
                  ·
                    refine ⟨3278087883938069340240281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8741567690501518240640749 3278087883938069340240281)
                    ·
                      refine ⟨2458565912953552005180211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278087883938069340240281 2458565912953552005180211)
                      ·
                        rfl

theorem cell23_4788040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_4788040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788040 prefixEnd_4788040 := by exact prefixLift 4788040
  have htrace : WordTrace (prefixWord ++ tailWord_4788040) baseStart_4788040 baseEnd_4788040 := by
    simpa [prefixWord, tailWord_4788040, baseEnd_4788040] using wordTrace_append hprefix tailTrace_4788040
  have hstable : (prefixWord ++ tailWord_4788040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788040).length < 2 ^ (prefixWord ++ tailWord_4788040).sum := by decide
  have hdescent : baseEnd_4788040 < baseStart_4788040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788056 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_4788056 : Nat := 118140960795 + 4788056 * 2 ^ 59
def prefixEnd_4788056 : Nat := 4983230072969 + 3 ^ 40 * 4788056 * 2
def baseEnd_4788056 : Nat := 2458574128644023942580137

theorem tailTrace_4788056 : CollatzResearch.WordTrace tailWord_4788056 prefixEnd_4788056 2458574128644023942580137 := by
  unfold tailWord_4788056
  simp only [CollatzResearch.WordTrace]
  refine ⟨87317374570849160853356011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116423166094465547804474681 87317374570849160853356011)
  ·
    refine ⟨130976061856273741280034017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87317374570849160853356011 130976061856273741280034017)
    ·
      refine ⟨98232046392205305960025513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130976061856273741280034017 98232046392205305960025513)
      ·
        refine ⟨73674034794153979470019135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98232046392205305960025513 73674034794153979470019135)
        ·
          refine ⟨110511052191230969205028703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73674034794153979470019135 110511052191230969205028703)
          ·
            refine ⟨165766578286846453807543055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110511052191230969205028703 165766578286846453807543055)
            ·
              refine ⟨248649867430269680711314583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165766578286846453807543055 248649867430269680711314583)
              ·
                refine ⟨372974801145404521066971875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248649867430269680711314583 372974801145404521066971875)
                ·
                  refine ⟨559462201718106781600457813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372974801145404521066971875 559462201718106781600457813)
                  ·
                    refine ⟨6556197676384063846880365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 559462201718106781600457813 6556197676384063846880365)
                    ·
                      refine ⟨2458574128644023942580137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6556197676384063846880365 2458574128644023942580137)
                      ·
                        rfl

theorem cell23_4788056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_4788056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788056 prefixEnd_4788056 := by exact prefixLift 4788056
  have htrace : WordTrace (prefixWord ++ tailWord_4788056) baseStart_4788056 baseEnd_4788056 := by
    simpa [prefixWord, tailWord_4788056, baseEnd_4788056] using wordTrace_append hprefix tailTrace_4788056
  have hstable : (prefixWord ++ tailWord_4788056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788056).length < 2 ^ (prefixWord ++ tailWord_4788056).sum := by decide
  have hdescent : baseEnd_4788056 < baseStart_4788056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788067 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 1, 5]
def baseStart_4788067 : Nat := 118140960795 + 4788067 * 2 ^ 59
def prefixEnd_4788067 : Nat := 4983230072969 + 3 ^ 40 * 4788067 * 2
def baseEnd_4788067 : Nat := 819526592310407799847529

theorem tailTrace_4788067 : CollatzResearch.WordTrace tailWord_4788067 prefixEnd_4788067 819526592310407799847529 := by
  unfold tailWord_4788067
  simp only [CollatzResearch.WordTrace]
  refine ⟨174635150344658470585362455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116423433563105647056908303 174635150344658470585362455)
  ·
    refine ⟨261952725516987705878043683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174635150344658470585362455 261952725516987705878043683)
    ·
      refine ⟨392929088275481558817065525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261952725516987705878043683 392929088275481558817065525)
      ·
        refine ⟨36837102025826396139099893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 392929088275481558817065525 36837102025826396139099893)
        ·
          refine ⟨3453478314921224638040615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36837102025826396139099893 3453478314921224638040615)
          ·
            refine ⟨5180217472381836957060923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453478314921224638040615 5180217472381836957060923)
            ·
              refine ⟨7770326208572755435591385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180217472381836957060923 7770326208572755435591385)
              ·
                refine ⟨5827744656429566576693539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7770326208572755435591385 5827744656429566576693539)
                ·
                  refine ⟨8741616984644349865040309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827744656429566576693539 8741616984644349865040309)
                  ·
                    refine ⟨819526592310407799847529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8741616984644349865040309 819526592310407799847529)
                    ·
                      rfl

theorem cell23_4788067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 5].length) (baseStart_4788067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788067 prefixEnd_4788067 := by exact prefixLift 4788067
  have htrace : WordTrace (prefixWord ++ tailWord_4788067) baseStart_4788067 baseEnd_4788067 := by
    simpa [prefixWord, tailWord_4788067, baseEnd_4788067] using wordTrace_append hprefix tailTrace_4788067
  have hstable : (prefixWord ++ tailWord_4788067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788067).length < 2 ^ (prefixWord ++ tailWord_4788067).sum := by decide
  have hdescent : baseEnd_4788067 < baseStart_4788067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788074 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4788074 : Nat := 118140960795 + 4788074 * 2 ^ 59
def prefixEnd_4788074 : Nat := 4983230072969 + 3 ^ 40 * 4788074 * 2
def baseEnd_4788074 : Nat := 2458583371295804872155055

theorem tailTrace_4788074 : CollatzResearch.WordTrace tailWord_4788074 prefixEnd_4788074 2458583371295804872155055 := by
  unfold tailWord_4788074
  simp only [CollatzResearch.WordTrace]
  refine ⟨43658851413908277695216819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116423603770422073853911517 43658851413908277695216819)
  ·
    refine ⟨65488277120862416542825229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43658851413908277695216819 65488277120862416542825229)
    ·
      refine ⟨24558103920323406203559461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65488277120862416542825229 24558103920323406203559461)
      ·
        refine ⟨4604644485060638663167399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24558103920323406203559461 4604644485060638663167399)
        ·
          refine ⟨6906966727590957994751099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4604644485060638663167399 6906966727590957994751099)
          ·
            refine ⟨10360450091386436992126649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6906966727590957994751099 10360450091386436992126649)
            ·
              refine ⟨7770337568539827744094987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10360450091386436992126649 7770337568539827744094987)
              ·
                refine ⟨11655506352809741616142481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7770337568539827744094987 11655506352809741616142481)
                ·
                  refine ⟨8741629764607306212106861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11655506352809741616142481 8741629764607306212106861)
                  ·
                    refine ⟨3278111161727739829540073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8741629764607306212106861 3278111161727739829540073)
                    ·
                      refine ⟨2458583371295804872155055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278111161727739829540073 2458583371295804872155055)
                      ·
                        rfl

theorem cell23_4788074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4788074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788074 prefixEnd_4788074 := by exact prefixLift 4788074
  have htrace : WordTrace (prefixWord ++ tailWord_4788074) baseStart_4788074 baseEnd_4788074 := by
    simpa [prefixWord, tailWord_4788074, baseEnd_4788074] using wordTrace_append hprefix tailTrace_4788074
  have hstable : (prefixWord ++ tailWord_4788074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788074).length < 2 ^ (prefixWord ++ tailWord_4788074).sum := by decide
  have hdescent : baseEnd_4788074 < baseStart_4788074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788076 : List Nat := [2, 2, 1, 1, 4, 2, 2, 9]
def baseStart_4788076 : Nat := 118140960795 + 4788076 * 2 ^ 59
def prefixEnd_4788076 : Nat := 4983230072969 + 3 ^ 40 * 4788076 * 2
def baseEnd_4788076 : Nat := 91058681416930143123335

theorem tailTrace_4788076 : CollatzResearch.WordTrace tailWord_4788076 prefixEnd_4788076 91058681416930143123335 := by
  unfold tailWord_4788076
  simp only [CollatzResearch.WordTrace]
  refine ⟨87317739300812932561220041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116423652401083910081626721 87317739300812932561220041)
  ·
    refine ⟨65488304475609699420915031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87317739300812932561220041 65488304475609699420915031)
    ·
      refine ⟨98232456713414549131372547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65488304475609699420915031 98232456713414549131372547)
      ·
        refine ⟨147348685070121823697058821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98232456713414549131372547 147348685070121823697058821)
        ·
          refine ⟨27627878450647841943198529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147348685070121823697058821 27627878450647841943198529)
          ·
            refine ⟨20720908837985881457398897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27627878450647841943198529 20720908837985881457398897)
            ·
              refine ⟨15540681628489411093049173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20720908837985881457398897 15540681628489411093049173)
              ·
                refine ⟨91058681416930143123335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15540681628489411093049173 91058681416930143123335)
                ·
                  rfl

theorem cell23_4788076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 9].length) (baseStart_4788076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788076 prefixEnd_4788076 := by exact prefixLift 4788076
  have htrace : WordTrace (prefixWord ++ tailWord_4788076) baseStart_4788076 baseEnd_4788076 := by
    simpa [prefixWord, tailWord_4788076, baseEnd_4788076] using wordTrace_append hprefix tailTrace_4788076
  have hstable : (prefixWord ++ tailWord_4788076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788076).length < 2 ^ (prefixWord ++ tailWord_4788076).sum := by decide
  have hdescent : baseEnd_4788076 < baseStart_4788076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788193 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_4788193 : Nat := 118140960795 + 4788193 * 2 ^ 59
def prefixEnd_4788193 : Nat := 4983230072969 + 3 ^ 40 * 4788193 * 2
def baseEnd_4788193 : Nat := 2458644475493689906567007

theorem tailTrace_4788193 : CollatzResearch.WordTrace tailWord_4788193 prefixEnd_4788193 2458644475493689906567007 := by
  unfold tailWord_4788193
  simp only [CollatzResearch.WordTrace]
  refine ⟨174639745942201994104449233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116426497294801329402966155 174639745942201994104449233)
  ·
    refine ⟨130979809456651495578336925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174639745942201994104449233 130979809456651495578336925)
    ·
      refine ⟨49117428546244310841876347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130979809456651495578336925 49117428546244310841876347)
      ·
        refine ⟨73676142819366466262814521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49117428546244310841876347 73676142819366466262814521)
        ·
          refine ⟨55257107114524849697110891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73676142819366466262814521 55257107114524849697110891)
          ·
            refine ⟨82885660671787274545666337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55257107114524849697110891 82885660671787274545666337)
            ·
              refine ⟨62164245503840455909249753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82885660671787274545666337 62164245503840455909249753)
              ·
                refine ⟨46623184127880341931937315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62164245503840455909249753 46623184127880341931937315)
                ·
                  refine ⟨69934776191820512897905973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46623184127880341931937315 69934776191820512897905973)
                  ·
                    refine ⟨6556385267983173084178685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69934776191820512897905973 6556385267983173084178685)
                    ·
                      refine ⟨2458644475493689906567007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6556385267983173084178685 2458644475493689906567007)
                      ·
                        rfl

theorem cell23_4788193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_4788193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788193 prefixEnd_4788193 := by exact prefixLift 4788193
  have htrace : WordTrace (prefixWord ++ tailWord_4788193) baseStart_4788193 baseEnd_4788193 := by
    simpa [prefixWord, tailWord_4788193, baseEnd_4788193] using wordTrace_append hprefix tailTrace_4788193
  have hstable : (prefixWord ++ tailWord_4788193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788193).length < 2 ^ (prefixWord ++ tailWord_4788193).sum := by decide
  have hdescent : baseEnd_4788193 < baseStart_4788193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788217 : List Nat := [1, 2, 1, 3, 1, 5, 3, 2, 5]
def baseStart_4788217 : Nat := 118140960795 + 4788217 * 2 ^ 59
def prefixEnd_4788217 : Nat := 4983230072969 + 3 ^ 40 * 4788217 * 2
def baseEnd_4788217 : Nat := 273184088781044201407433

theorem tailTrace_4788217 : CollatzResearch.WordTrace tailWord_4788217 prefixEnd_4788217 273184088781044201407433 := by
  unfold tailWord_4788217
  simp only [CollatzResearch.WordTrace]
  refine ⟨174640621294115046203322905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116427080862743364135548603 174640621294115046203322905)
  ·
    refine ⟨130980465970586284652492179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174640621294115046203322905 130980465970586284652492179)
    ·
      refine ⟨196470698955879426978738269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130980465970586284652492179 196470698955879426978738269)
      ·
        refine ⟨73676512108454785117026851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196470698955879426978738269 73676512108454785117026851)
        ·
          refine ⟨110514768162682177675540277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73676512108454785117026851 110514768162682177675540277)
          ·
            refine ⟨10360759515251454157081901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110514768162682177675540277 10360759515251454157081901)
            ·
              refine ⟨3885284818219295308905713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10360759515251454157081901 3885284818219295308905713)
              ·
                refine ⟨2913963613664471481679285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3885284818219295308905713 2913963613664471481679285)
                ·
                  refine ⟨273184088781044201407433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2913963613664471481679285 273184088781044201407433)
                  ·
                    rfl

theorem cell23_4788217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 5].length) (baseStart_4788217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788217 prefixEnd_4788217 := by exact prefixLift 4788217
  have htrace : WordTrace (prefixWord ++ tailWord_4788217) baseStart_4788217 baseEnd_4788217 := by
    simpa [prefixWord, tailWord_4788217, baseEnd_4788217] using wordTrace_append hprefix tailTrace_4788217
  have hstable : (prefixWord ++ tailWord_4788217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788217).length < 2 ^ (prefixWord ++ tailWord_4788217).sum := by decide
  have hdescent : baseEnd_4788217 < baseStart_4788217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788220 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_4788220 : Nat := 118140960795 + 4788220 * 2 ^ 59
def prefixEnd_4788220 : Nat := 4983230072969 + 3 ^ 40 * 4788220 * 2
def baseEnd_4788220 : Nat := 2458658339471361300929383

theorem tailTrace_4788220 : CollatzResearch.WordTrace tailWord_4788220 prefixEnd_4788220 2458658339471361300929383 := by
  unfold tailWord_4788220
  simp only [CollatzResearch.WordTrace]
  refine ⟨87320365356552088857841057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116427153808736118477121409 87320365356552088857841057)
  ·
    refine ⟨65490274017414066643380793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87320365356552088857841057 65490274017414066643380793)
    ·
      refine ⟨49117705513060549982535595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65490274017414066643380793 49117705513060549982535595)
      ·
        refine ⟨73676558269590824973803393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49117705513060549982535595 73676558269590824973803393)
        ·
          refine ⟨55257418702193118730352545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73676558269590824973803393 55257418702193118730352545)
          ·
            refine ⟨41443064026644839047764409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55257418702193118730352545 41443064026644839047764409)
            ·
              refine ⟨31082298019983629285823307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41443064026644839047764409 31082298019983629285823307)
              ·
                refine ⟨46623447029975443928734961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31082298019983629285823307 46623447029975443928734961)
                ·
                  refine ⟨34967585272481582946551221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46623447029975443928734961 34967585272481582946551221)
                  ·
                    refine ⟨3278211119295148401239177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34967585272481582946551221 3278211119295148401239177)
                    ·
                      refine ⟨2458658339471361300929383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278211119295148401239177 2458658339471361300929383)
                      ·
                        rfl

theorem cell23_4788220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_4788220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788220 prefixEnd_4788220 := by exact prefixLift 4788220
  have htrace : WordTrace (prefixWord ++ tailWord_4788220) baseStart_4788220 baseEnd_4788220 := by
    simpa [prefixWord, tailWord_4788220, baseEnd_4788220] using wordTrace_append hprefix tailTrace_4788220
  have hstable : (prefixWord ++ tailWord_4788220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788220).length < 2 ^ (prefixWord ++ tailWord_4788220).sum := by decide
  have hdescent : baseEnd_4788220 < baseStart_4788220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788247 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 2, 5]
def baseStart_4788247 : Nat := 118140960795 + 4788247 * 2 ^ 59
def prefixEnd_4788247 : Nat := 4983230072969 + 3 ^ 40 * 4788247 * 2
def baseEnd_4788247 : Nat := 819557401149677565097253

theorem tailTrace_4788247 : CollatzResearch.WordTrace tailWord_4788247 prefixEnd_4788247 819557401149677565097253 := by
  unfold tailWord_4788247
  simp only [CollatzResearch.WordTrace]
  refine ⟨174641715484006361326914995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116427810322670907551276663 174641715484006361326914995)
  ·
    refine ⟨261962573226009541990372493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174641715484006361326914995 261962573226009541990372493)
    ·
      refine ⟨98235964959753578246389685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261962573226009541990372493 98235964959753578246389685)
      ·
        refine ⟨9209621714976897960599033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98235964959753578246389685 9209621714976897960599033)
        ·
          refine ⟨6907216286232673470449275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9209621714976897960599033 6907216286232673470449275)
          ·
            refine ⟨10360824429349010205673913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6907216286232673470449275 10360824429349010205673913)
            ·
              refine ⟨7770618322011757654255435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10360824429349010205673913 7770618322011757654255435)
              ·
                refine ⟨11655927483017636481383153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7770618322011757654255435 11655927483017636481383153)
                ·
                  refine ⟨8741945612263227361037365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11655927483017636481383153 8741945612263227361037365)
                  ·
                    refine ⟨819557401149677565097253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8741945612263227361037365 819557401149677565097253)
                    ·
                      rfl

theorem cell23_4788247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_4788247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788247 prefixEnd_4788247 := by exact prefixLift 4788247
  have htrace : WordTrace (prefixWord ++ tailWord_4788247) baseStart_4788247 baseEnd_4788247 := by
    simpa [prefixWord, tailWord_4788247, baseEnd_4788247] using wordTrace_append hprefix tailTrace_4788247
  have hstable : (prefixWord ++ tailWord_4788247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788247).length < 2 ^ (prefixWord ++ tailWord_4788247).sum := by decide
  have hdescent : baseEnd_4788247 < baseStart_4788247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788250 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_4788250 : Nat := 118140960795 + 4788250 * 2 ^ 59
def prefixEnd_4788250 : Nat := 4983230072969 + 3 ^ 40 * 4788250 * 2
def baseEnd_4788250 : Nat := 2458673743890996183554245

theorem tailTrace_4788250 : CollatzResearch.WordTrace tailWord_4788250 prefixEnd_4788250 2458673743890996183554245 := by
  unfold tailWord_4788250
  simp only [CollatzResearch.WordTrace]
  refine ⟨43660456225748873209818551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116427883268663661892849469 43660456225748873209818551)
  ·
    refine ⟨65490684338623309814727827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43660456225748873209818551 65490684338623309814727827)
    ·
      refine ⟨98236026507934964722091741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65490684338623309814727827 98236026507934964722091741)
      ·
        refine ⟨36838509940475611770784403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98236026507934964722091741 36838509940475611770784403)
        ·
          refine ⟨55257764910713417656176605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36838509940475611770784403 55257764910713417656176605)
          ·
            refine ⟨20721661841517531621066227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55257764910713417656176605 20721661841517531621066227)
            ·
              refine ⟨31082492762276297431599341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20721661841517531621066227 31082492762276297431599341)
              ·
                refine ⟨11655934785853611536849753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31082492762276297431599341 11655934785853611536849753)
                ·
                  refine ⟨8741951089390208652637315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11655934785853611536849753 8741951089390208652637315)
                  ·
                    refine ⟨13112926634085312978955973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8741951089390208652637315 13112926634085312978955973)
                    ·
                      refine ⟨2458673743890996183554245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13112926634085312978955973 2458673743890996183554245)
                      ·
                        rfl

theorem cell23_4788250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_4788250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788250 prefixEnd_4788250 := by exact prefixLift 4788250
  have htrace : WordTrace (prefixWord ++ tailWord_4788250) baseStart_4788250 baseEnd_4788250 := by
    simpa [prefixWord, tailWord_4788250, baseEnd_4788250] using wordTrace_append hprefix tailTrace_4788250
  have hstable : (prefixWord ++ tailWord_4788250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788250).length < 2 ^ (prefixWord ++ tailWord_4788250).sum := by decide
  have hdescent : baseEnd_4788250 < baseStart_4788250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788294 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_4788294 : Nat := 118140960795 + 4788294 * 2 ^ 59
def prefixEnd_4788294 : Nat := 4983230072969 + 3 ^ 40 * 4788294 * 2
def baseEnd_4788294 : Nat := 819565445679931337134681

theorem tailTrace_4788294 : CollatzResearch.WordTrace tailWord_4788294 prefixEnd_4788294 819565445679931337134681 := by
  unfold tailWord_4788294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457607178588627761058623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116428953143224058902583957 5457607178588627761058623)
  ·
    refine ⟨8186410767882941641587935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5457607178588627761058623 8186410767882941641587935)
    ·
      refine ⟨12279616151824412462381903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8186410767882941641587935 12279616151824412462381903)
      ·
        refine ⟨18419424227736618693572855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12279616151824412462381903 18419424227736618693572855)
        ·
          refine ⟨27629136341604928040359283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18419424227736618693572855 27629136341604928040359283)
          ·
            refine ⟨41443704512407392060538925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27629136341604928040359283 41443704512407392060538925)
            ·
              refine ⟨15541389192152772022702097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41443704512407392060538925 15541389192152772022702097)
              ·
                refine ⟨11656041894114579017026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15541389192152772022702097 11656041894114579017026573)
                ·
                  refine ⟨4371015710292967131384965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11656041894114579017026573 4371015710292967131384965)
                  ·
                    refine ⟨819565445679931337134681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4371015710292967131384965 819565445679931337134681)
                    ·
                      rfl

theorem cell23_4788294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_4788294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788294 prefixEnd_4788294 := by exact prefixLift 4788294
  have htrace : WordTrace (prefixWord ++ tailWord_4788294) baseStart_4788294 baseEnd_4788294 := by
    simpa [prefixWord, tailWord_4788294, baseEnd_4788294] using wordTrace_append hprefix tailTrace_4788294
  have hstable : (prefixWord ++ tailWord_4788294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788294).length < 2 ^ (prefixWord ++ tailWord_4788294).sum := by decide
  have hdescent : baseEnd_4788294 < baseStart_4788294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788327 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_4788327 : Nat := 118140960795 + 4788327 * 2 ^ 59
def prefixEnd_4788327 : Nat := 4983230072969 + 3 ^ 40 * 4788327 * 2
def baseEnd_4788327 : Nat := 2458713281901392382291391

theorem tailTrace_4788327 : CollatzResearch.WordTrace tailWord_4788327 prefixEnd_4788327 2458713281901392382291391 := by
  unfold tailWord_4788327
  simp only [CollatzResearch.WordTrace]
  refine ⟨174644633323716534989827235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116429755549144356659884823 174644633323716534989827235)
  ·
    refine ⟨261966949985574802484740853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174644633323716534989827235 261966949985574802484740853)
    ·
      refine ⟨24559401561147637732944455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261966949985574802484740853 24559401561147637732944455)
      ·
        refine ⟨36839102341721456599416683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24559401561147637732944455 36839102341721456599416683)
        ·
          refine ⟨55258653512582184899125025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36839102341721456599416683 55258653512582184899125025)
          ·
            refine ⟨41443990134436638674343769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55258653512582184899125025 41443990134436638674343769)
            ·
              refine ⟨31082992600827479005757827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41443990134436638674343769 31082992600827479005757827)
              ·
                refine ⟨46624488901241218508636741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31082992600827479005757827 46624488901241218508636741)
                ·
                  refine ⟨8742091668982728470369389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46624488901241218508636741 8742091668982728470369389)
                  ·
                    refine ⟨3278284375868523176388521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8742091668982728470369389 3278284375868523176388521)
                    ·
                      refine ⟨2458713281901392382291391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278284375868523176388521 2458713281901392382291391)
                      ·
                        rfl

theorem cell23_4788327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_4788327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788327 prefixEnd_4788327 := by exact prefixLift 4788327
  have htrace : WordTrace (prefixWord ++ tailWord_4788327) baseStart_4788327 baseEnd_4788327 := by
    simpa [prefixWord, tailWord_4788327, baseEnd_4788327] using wordTrace_append hprefix tailTrace_4788327
  have hstable : (prefixWord ++ tailWord_4788327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788327).length < 2 ^ (prefixWord ++ tailWord_4788327).sum := by decide
  have hdescent : baseEnd_4788327 < baseStart_4788327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788334 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4788334 : Nat := 118140960795 + 4788334 * 2 ^ 59
def prefixEnd_4788334 : Nat := 4983230072969 + 3 ^ 40 * 4788334 * 2
def baseEnd_4788334 : Nat := 2458716876265973854903859

theorem tailTrace_4788334 : CollatzResearch.WordTrace tailWord_4788334 prefixEnd_4788334 2458716876265973854903859 := by
  unfold tailWord_4788334
  simp only [CollatzResearch.WordTrace]
  refine ⟨21830611079336396898166507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116429925756460783456888037 21830611079336396898166507)
  ·
    refine ⟨32745916619004595347249761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21830611079336396898166507 32745916619004595347249761)
    ·
      refine ⟨24559437464253446510437321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32745916619004595347249761 24559437464253446510437321)
      ·
        refine ⟨18419578098190084882827991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24559437464253446510437321 18419578098190084882827991)
        ·
          refine ⟨27629367147285127324241987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18419578098190084882827991 27629367147285127324241987)
          ·
            refine ⟨41444050720927690986362981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27629367147285127324241987 41444050720927690986362981)
            ·
              refine ⟨7770759510173942059943059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41444050720927690986362981 7770759510173942059943059)
              ·
                refine ⟨11656139265260913089914589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7770759510173942059943059 11656139265260913089914589)
                ·
                  refine ⟨4371052224472842408717971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11656139265260913089914589 4371052224472842408717971)
                  ·
                    refine ⟨6556578336709263613076957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4371052224472842408717971 6556578336709263613076957)
                    ·
                      refine ⟨2458716876265973854903859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6556578336709263613076957 2458716876265973854903859)
                      ·
                        rfl

theorem cell23_4788334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4788334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788334 prefixEnd_4788334 := by exact prefixLift 4788334
  have htrace : WordTrace (prefixWord ++ tailWord_4788334) baseStart_4788334 baseEnd_4788334 := by
    simpa [prefixWord, tailWord_4788334, baseEnd_4788334] using wordTrace_append hprefix tailTrace_4788334
  have hstable : (prefixWord ++ tailWord_4788334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788334).length < 2 ^ (prefixWord ++ tailWord_4788334).sum := by decide
  have hdescent : baseEnd_4788334 < baseStart_4788334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788357 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_4788357 : Nat := 118140960795 + 4788357 * 2 ^ 59
def prefixEnd_4788357 : Nat := 4983230072969 + 3 ^ 40 * 4788357 * 2
def baseEnd_4788357 : Nat := 2458728686321027264916253

theorem tailTrace_4788357 : CollatzResearch.WordTrace tailWord_4788357 prefixEnd_4788357 2458728686321027264916253 := by
  unfold tailWord_4788357
  simp only [CollatzResearch.WordTrace]
  refine ⟨174645727513607850113419325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116430485009071900075612883 174645727513607850113419325)
  ·
    refine ⟨65492147817602943792532247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174645727513607850113419325 65492147817602943792532247)
    ·
      refine ⟨98238221726404415688798371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65492147817602943792532247 98238221726404415688798371)
      ·
        refine ⟨147357332589606623533197557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98238221726404415688798371 147357332589606623533197557)
        ·
          refine ⟨13814749930275620956237271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147357332589606623533197557 13814749930275620956237271)
          ·
            refine ⟨20722124895413431434355907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13814749930275620956237271 20722124895413431434355907)
            ·
              refine ⟨31083187343120147151533861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20722124895413431434355907 31083187343120147151533861)
              ·
                refine ⟨5828097626835027590912599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31083187343120147151533861 5828097626835027590912599)
                ·
                  refine ⟨8742146440252541386368899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5828097626835027590912599 8742146440252541386368899)
                  ·
                    refine ⟨13113219660378812079553349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8742146440252541386368899 13113219660378812079553349)
                    ·
                      refine ⟨2458728686321027264916253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13113219660378812079553349 2458728686321027264916253)
                      ·
                        rfl

theorem cell23_4788357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_4788357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788357 prefixEnd_4788357 := by exact prefixLift 4788357
  have htrace : WordTrace (prefixWord ++ tailWord_4788357) baseStart_4788357 baseEnd_4788357 := by
    simpa [prefixWord, tailWord_4788357, baseEnd_4788357] using wordTrace_append hprefix tailTrace_4788357
  have hstable : (prefixWord ++ tailWord_4788357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788357).length < 2 ^ (prefixWord ++ tailWord_4788357).sum := by decide
  have hdescent : baseEnd_4788357 < baseStart_4788357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788397 : List Nat := [1, 5, 2, 1, 2, 2, 2, 8]
def baseStart_4788397 : Nat := 118140960795 + 4788397 * 2 ^ 59
def prefixEnd_4788397 : Nat := 4983230072969 + 3 ^ 40 * 4788397 * 2
def baseEnd_4788397 : Nat := 91064786131378041052447

theorem tailTrace_4788397 : CollatzResearch.WordTrace tailWord_4788397 prefixEnd_4788397 91064786131378041052447 := by
  unfold tailWord_4788397
  simp only [CollatzResearch.WordTrace]
  refine ⟨174647186433462936944875445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116431457622308624629916963 174647186433462936944875445)
  ·
    refine ⟨16373173728137150338582073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174647186433462936944875445 16373173728137150338582073)
    ·
      refine ⟨12279880296102862753936555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16373173728137150338582073 12279880296102862753936555)
      ·
        refine ⟨18419820444154294130904833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12279880296102862753936555 18419820444154294130904833)
        ·
          refine ⟨13814865333115720598178625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18419820444154294130904833 13814865333115720598178625)
          ·
            refine ⟨10361148999836790448633969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13814865333115720598178625 10361148999836790448633969)
            ·
              refine ⟨7770861749877592836475477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10361148999836790448633969 7770861749877592836475477)
              ·
                refine ⟨91064786131378041052447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7770861749877592836475477 91064786131378041052447)
                ·
                  rfl

theorem cell23_4788397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 8].length) (baseStart_4788397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788397 prefixEnd_4788397 := by exact prefixLift 4788397
  have htrace : WordTrace (prefixWord ++ tailWord_4788397) baseStart_4788397 baseEnd_4788397 := by
    simpa [prefixWord, tailWord_4788397, baseEnd_4788397] using wordTrace_append hprefix tailTrace_4788397
  have hstable : (prefixWord ++ tailWord_4788397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788397).length < 2 ^ (prefixWord ++ tailWord_4788397).sum := by decide
  have hdescent : baseEnd_4788397 < baseStart_4788397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788428 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4788428 : Nat := 118140960795 + 4788428 * 2 ^ 59
def prefixEnd_4788428 : Nat := 4983230072969 + 3 ^ 40 * 4788428 * 2
def baseEnd_4788428 : Nat := 2458765143447496487128427

theorem tailTrace_4788428 : CollatzResearch.WordTrace tailWord_4788428 prefixEnd_4788428 2458765143447496487128427 := by
  unfold tailWord_4788428
  simp only [CollatzResearch.WordTrace]
  refine ⟨87324158548175314619626969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116432211397567086159502625 87324158548175314619626969)
  ·
    refine ⟨65493118911131485964720227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87324158548175314619626969 65493118911131485964720227)
    ·
      refine ⟨98239678366697228947080341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65493118911131485964720227 98239678366697228947080341)
      ·
        refine ⟨4604984923438932606894391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98239678366697228947080341 4604984923438932606894391)
        ·
          refine ⟨6907477385158398910341587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4604984923438932606894391 6907477385158398910341587)
          ·
            refine ⟨10361216077737598365512381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6907477385158398910341587 10361216077737598365512381)
            ·
              refine ⟨3885456029151599387067143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10361216077737598365512381 3885456029151599387067143)
              ·
                refine ⟨5828184043727399080600715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3885456029151599387067143 5828184043727399080600715)
                ·
                  refine ⟨8742276065591098620901073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5828184043727399080600715 8742276065591098620901073)
                  ·
                    refine ⟨6556707049193323965675805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8742276065591098620901073 6556707049193323965675805)
                    ·
                      refine ⟨2458765143447496487128427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6556707049193323965675805 2458765143447496487128427)
                      ·
                        rfl

theorem cell23_4788428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4788428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788428 prefixEnd_4788428 := by exact prefixLift 4788428
  have htrace : WordTrace (prefixWord ++ tailWord_4788428) baseStart_4788428 baseEnd_4788428 := by
    simpa [prefixWord, tailWord_4788428, baseEnd_4788428] using wordTrace_append hprefix tailTrace_4788428
  have hstable : (prefixWord ++ tailWord_4788428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788428).length < 2 ^ (prefixWord ++ tailWord_4788428).sum := by decide
  have hdescent : baseEnd_4788428 < baseStart_4788428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788447 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 5, 4, 2]
def baseStart_4788447 : Nat := 118140960795 + 4788447 * 2 ^ 59
def prefixEnd_4788447 : Nat := 4983230072969 + 3 ^ 40 * 4788447 * 2
def baseEnd_4788447 : Nat := 2458774899579931912790839

theorem tailTrace_4788447 : CollatzResearch.WordTrace tailWord_4788447 prefixEnd_4788447 2458774899579931912790839 := by
  unfold tailWord_4788447
  simp only [CollatzResearch.WordTrace]
  refine ⟨174649010083281795484195595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116432673388854530322797063 174649010083281795484195595)
  ·
    refine ⟨261973515124922693226293393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174649010083281795484195595 261973515124922693226293393)
    ·
      refine ⟨196480136343692019919720045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261973515124922693226293393 196480136343692019919720045)
      ·
        refine ⟨73680051128884507469895017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196480136343692019919720045 73680051128884507469895017)
        ·
          refine ⟨55260038346663380602421263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73680051128884507469895017 55260038346663380602421263)
          ·
            refine ⟨82890057519995070903631895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55260038346663380602421263 82890057519995070903631895)
            ·
              refine ⟨124335086279992606355447843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82890057519995070903631895 124335086279992606355447843)
              ·
                refine ⟨186502629419988909533171765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124335086279992606355447843 186502629419988909533171765)
                ·
                  refine ⟨17484621508123960268734853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186502629419988909533171765 17484621508123960268734853)
                  ·
                    refine ⟨3278366532773242550387785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17484621508123960268734853 3278366532773242550387785)
                    ·
                      refine ⟨2458774899579931912790839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278366532773242550387785 2458774899579931912790839)
                      ·
                        rfl

theorem cell23_4788447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_4788447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788447 prefixEnd_4788447 := by exact prefixLift 4788447
  have htrace : WordTrace (prefixWord ++ tailWord_4788447) baseStart_4788447 baseEnd_4788447 := by
    simpa [prefixWord, tailWord_4788447, baseEnd_4788447] using wordTrace_append hprefix tailTrace_4788447
  have hstable : (prefixWord ++ tailWord_4788447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788447).length < 2 ^ (prefixWord ++ tailWord_4788447).sum := by decide
  have hdescent : baseEnd_4788447 < baseStart_4788447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788497 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_4788497 : Nat := 118140960795 + 4788497 * 2 ^ 59
def prefixEnd_4788497 : Nat := 4983230072969 + 3 ^ 40 * 4788497 * 2
def baseEnd_4788497 : Nat := 2458800573612656717165609

theorem tailTrace_4788497 : CollatzResearch.WordTrace tailWord_4788497 prefixEnd_4788497 2458800573612656717165609 := by
  unfold tailWord_4788497
  simp only [CollatzResearch.WordTrace]
  refine ⟨174650833733100654023515745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116433889155400436015677163 174650833733100654023515745)
  ·
    refine ⟨130988125299825490517636809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174650833733100654023515745 130988125299825490517636809)
    ·
      refine ⟨98241093974869117888227607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130988125299825490517636809 98241093974869117888227607)
      ·
        refine ⟨147361640962303676832341411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98241093974869117888227607 147361640962303676832341411)
        ·
          refine ⟨221042461443455515248512117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147361640962303676832341411 221042461443455515248512117)
          ·
            refine ⟨20722730760323954554548011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221042461443455515248512117 20722730760323954554548011)
            ·
              refine ⟨31084096140485931831822017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20722730760323954554548011 31084096140485931831822017)
              ·
                refine ⟨23313072105364448873866513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31084096140485931831822017 23313072105364448873866513)
                ·
                  refine ⟨17484804079023336655399885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23313072105364448873866513 17484804079023336655399885)
                  ·
                    refine ⟨6556801529633751245774957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17484804079023336655399885 6556801529633751245774957)
                    ·
                      refine ⟨2458800573612656717165609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6556801529633751245774957 2458800573612656717165609)
                      ·
                        rfl

theorem cell23_4788497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_4788497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788497 prefixEnd_4788497 := by exact prefixLift 4788497
  have htrace : WordTrace (prefixWord ++ tailWord_4788497) baseStart_4788497 baseEnd_4788497 := by
    simpa [prefixWord, tailWord_4788497, baseEnd_4788497] using wordTrace_append hprefix tailTrace_4788497
  have hstable : (prefixWord ++ tailWord_4788497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788497).length < 2 ^ (prefixWord ++ tailWord_4788497).sum := by decide
  have hdescent : baseEnd_4788497 < baseStart_4788497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788507 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 7, 2]
def baseStart_4788507 : Nat := 118140960795 + 4788507 * 2 ^ 59
def prefixEnd_4788507 : Nat := 4983230072969 + 3 ^ 40 * 4788507 * 2
def baseEnd_4788507 : Nat := 2458805708419201678040563

theorem tailTrace_4788507 : CollatzResearch.WordTrace tailWord_4788507 prefixEnd_4788507 2458805708419201678040563 := by
  unfold tailWord_4788507
  simp only [CollatzResearch.WordTrace]
  refine ⟨174651198463064425731379775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116434132308709617154253183 174651198463064425731379775)
  ·
    refine ⟨261976797694596638597069663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174651198463064425731379775 261976797694596638597069663)
    ·
      refine ⟨392965196541894957895604495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261976797694596638597069663 392965196541894957895604495)
      ·
        refine ⟨589447794812842436843406743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392965196541894957895604495 589447794812842436843406743)
        ·
          refine ⟨884171692219263655265110115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589447794812842436843406743 884171692219263655265110115)
          ·
            refine ⟨1326257538328895482897665173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884171692219263655265110115 1326257538328895482897665173)
            ·
              refine ⟨62168322109166975760828055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1326257538328895482897665173 62168322109166975760828055)
              ·
                refine ⟨93252483163750463641242083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62168322109166975760828055 93252483163750463641242083)
                ·
                  refine ⟨139878724745625695461863125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93252483163750463641242083 139878724745625695461863125)
                  ·
                    refine ⟨3278407611225602237387417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 139878724745625695461863125 3278407611225602237387417)
                    ·
                      refine ⟨2458805708419201678040563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278407611225602237387417 2458805708419201678040563)
                      ·
                        rfl

theorem cell23_4788507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7, 2].length) (baseStart_4788507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788507 prefixEnd_4788507 := by exact prefixLift 4788507
  have htrace : WordTrace (prefixWord ++ tailWord_4788507) baseStart_4788507 baseEnd_4788507 := by
    simpa [prefixWord, tailWord_4788507, baseEnd_4788507] using wordTrace_append hprefix tailTrace_4788507
  have hstable : (prefixWord ++ tailWord_4788507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788507).length < 2 ^ (prefixWord ++ tailWord_4788507).sum := by decide
  have hdescent : baseEnd_4788507 < baseStart_4788507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788514 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_4788514 : Nat := 118140960795 + 4788514 * 2 ^ 59
def prefixEnd_4788514 : Nat := 4983230072969 + 3 ^ 40 * 4788514 * 2
def baseEnd_4788514 : Nat := 2458809302783783150653031

theorem tailTrace_4788514 : CollatzResearch.WordTrace tailWord_4788514 prefixEnd_4788514 2458809302783783150653031 := by
  unfold tailWord_4788514
  simp only [CollatzResearch.WordTrace]
  refine ⟨43662863443509766481721149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116434302516026043951256397 43662863443509766481721149)
  ·
    refine ⟨16373573791316162430645431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43662863443509766481721149 16373573791316162430645431)
    ·
      refine ⟨24560360686974243645968147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16373573791316162430645431 24560360686974243645968147)
      ·
        refine ⟨36840541030461365468952221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24560360686974243645968147 36840541030461365468952221)
        ·
          refine ⟨13815202886423012050857083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36840541030461365468952221 13815202886423012050857083)
          ·
            refine ⟨20722804329634518076285625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13815202886423012050857083 20722804329634518076285625)
            ·
              refine ⟨15542103247225888557214219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20722804329634518076285625 15542103247225888557214219)
              ·
                refine ⟨23313154870838832835821329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15542103247225888557214219 23313154870838832835821329)
                ·
                  refine ⟨17484866153129124626865997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23313154870838832835821329 17484866153129124626865997)
                  ·
                    refine ⟨6556824807423421735074749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17484866153129124626865997 6556824807423421735074749)
                    ·
                      refine ⟨2458809302783783150653031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6556824807423421735074749 2458809302783783150653031)
                      ·
                        rfl

theorem cell23_4788514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_4788514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788514 prefixEnd_4788514 := by exact prefixLift 4788514
  have htrace : WordTrace (prefixWord ++ tailWord_4788514) baseStart_4788514 baseEnd_4788514 := by
    simpa [prefixWord, tailWord_4788514, baseEnd_4788514] using wordTrace_append hprefix tailTrace_4788514
  have hstable : (prefixWord ++ tailWord_4788514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788514).length < 2 ^ (prefixWord ++ tailWord_4788514).sum := by decide
  have hdescent : baseEnd_4788514 < baseStart_4788514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788547 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 5, 4]
def baseStart_4788547 : Nat := 118140960795 + 4788547 * 2 ^ 59
def prefixEnd_4788547 : Nat := 4983230072969 + 3 ^ 40 * 4788547 * 2
def baseEnd_4788547 : Nat := 819608749215127173846793

theorem tailTrace_4788547 : CollatzResearch.WordTrace tailWord_4788547 prefixEnd_4788547 819608749215127173846793 := by
  unfold tailWord_4788547
  simp only [CollatzResearch.WordTrace]
  refine ⟨174652657382919512562835895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116435104921946341708557263 174652657382919512562835895)
  ·
    refine ⟨261978986074379268844253843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174652657382919512562835895 261978986074379268844253843)
    ·
      refine ⟨392968479111568903266380765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261978986074379268844253843 392968479111568903266380765)
      ·
        refine ⟨147363179666838338724892787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392968479111568903266380765 147363179666838338724892787)
        ·
          refine ⟨221044769500257508087339181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147363179666838338724892787 221044769500257508087339181)
          ·
            refine ⟨82891788562596565532752193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221044769500257508087339181 82891788562596565532752193)
            ·
              refine ⟨62168841421947424149564145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82891788562596565532752193 62168841421947424149564145)
              ·
                refine ⟨46626631066460568112173109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62168841421947424149564145 46626631066460568112173109)
                ·
                  refine ⟨4371246662480678260516229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46626631066460568112173109 4371246662480678260516229)
                  ·
                    refine ⟨819608749215127173846793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4371246662480678260516229 819608749215127173846793)
                    ·
                      rfl

theorem cell23_4788547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 4].length) (baseStart_4788547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788547 prefixEnd_4788547 := by exact prefixLift 4788547
  have htrace : WordTrace (prefixWord ++ tailWord_4788547) baseStart_4788547 baseEnd_4788547 := by
    simpa [prefixWord, tailWord_4788547, baseEnd_4788547] using wordTrace_append hprefix tailTrace_4788547
  have hstable : (prefixWord ++ tailWord_4788547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788547).length < 2 ^ (prefixWord ++ tailWord_4788547).sum := by decide
  have hdescent : baseEnd_4788547 < baseStart_4788547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788604 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_4788604 : Nat := 118140960795 + 4788604 * 2 ^ 59
def prefixEnd_4788604 : Nat := 4983230072969 + 3 ^ 40 * 4788604 * 2
def baseEnd_4788604 : Nat := 2458855516042687798527617

theorem tailTrace_4788604 : CollatzResearch.WordTrace tailWord_4788604 prefixEnd_4788604 2458855516042687798527617 := by
  unfold tailWord_4788604
  simp only [CollatzResearch.WordTrace]
  refine ⟨87327368171856505648830433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116436490895808674198440577 87327368171856505648830433)
  ·
    refine ⟨65495526128892379236622825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87327368171856505648830433 65495526128892379236622825)
    ·
      refine ⟨49121644596669284427467119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65495526128892379236622825 49121644596669284427467119)
      ·
        refine ⟨73682466895003926641200679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49121644596669284427467119 73682466895003926641200679)
        ·
          refine ⟨110523700342505889961801019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73682466895003926641200679 110523700342505889961801019)
          ·
            refine ⟨165785550513758834942701529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110523700342505889961801019 165785550513758834942701529)
            ·
              refine ⟨124339162885319126207026147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165785550513758834942701529 124339162885319126207026147)
              ·
                refine ⟨186508744327978689310539221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124339162885319126207026147 186508744327978689310539221)
                ·
                  refine ⟨4371298695187000530715763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 186508744327978689310539221 4371298695187000530715763)
                  ·
                    refine ⟨6556948042780500796073645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4371298695187000530715763 6556948042780500796073645)
                    ·
                      refine ⟨2458855516042687798527617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6556948042780500796073645 2458855516042687798527617)
                      ·
                        rfl

theorem cell23_4788604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_4788604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788604 prefixEnd_4788604 := by exact prefixLift 4788604
  have htrace : WordTrace (prefixWord ++ tailWord_4788604) baseStart_4788604 baseEnd_4788604 := by
    simpa [prefixWord, tailWord_4788604, baseEnd_4788604] using wordTrace_append hprefix tailTrace_4788604
  have hstable : (prefixWord ++ tailWord_4788604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788604).length < 2 ^ (prefixWord ++ tailWord_4788604).sum := by decide
  have hdescent : baseEnd_4788604 < baseStart_4788604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788638 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4788638 : Nat := 118140960795 + 4788638 * 2 ^ 59
def prefixEnd_4788638 : Nat := 4983230072969 + 3 ^ 40 * 4788638 * 2
def baseEnd_4788638 : Nat := 2458872974384940665502461

theorem tailTrace_4788638 : CollatzResearch.WordTrace tailWord_4788638 prefixEnd_4788638 2458872974384940665502461 := by
  unfold tailWord_4788638
  simp only [CollatzResearch.WordTrace]
  refine ⟨21831997053198729388049821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116437317617059890069599045 21831997053198729388049821)
  ·
    refine ⟨8186998894949523520518683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21831997053198729388049821 8186998894949523520518683)
    ·
      refine ⟨12280498342424285280778025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8186998894949523520518683 12280498342424285280778025)
      ·
        refine ⟨9210373756818213960583519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12280498342424285280778025 9210373756818213960583519)
        ·
          refine ⟨13815560635227320940875279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9210373756818213960583519 13815560635227320940875279)
          ·
            refine ⟨20723340952840981411312919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13815560635227320940875279 20723340952840981411312919)
            ·
              refine ⟨31085011429261472116969379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20723340952840981411312919 31085011429261472116969379)
              ·
                refine ⟨46627517143892208175454069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31085011429261472116969379 46627517143892208175454069)
                ·
                  refine ⟨4371329732239894516448819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46627517143892208175454069 4371329732239894516448819)
                  ·
                    refine ⟨6556994598359841774673229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4371329732239894516448819 6556994598359841774673229)
                    ·
                      refine ⟨2458872974384940665502461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6556994598359841774673229 2458872974384940665502461)
                      ·
                        rfl

theorem cell23_4788638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4788638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788638 prefixEnd_4788638 := by exact prefixLift 4788638
  have htrace : WordTrace (prefixWord ++ tailWord_4788638) baseStart_4788638 baseEnd_4788638 := by
    simpa [prefixWord, tailWord_4788638, baseEnd_4788638] using wordTrace_append hprefix tailTrace_4788638
  have hstable : (prefixWord ++ tailWord_4788638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788638).length < 2 ^ (prefixWord ++ tailWord_4788638).sum := by decide
  have hdescent : baseEnd_4788638 < baseStart_4788638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788644 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_4788644 : Nat := 118140960795 + 4788644 * 2 ^ 59
def prefixEnd_4788644 : Nat := 4983230072969 + 3 ^ 40 * 4788644 * 2
def baseEnd_4788644 : Nat := 2458876055268867642027433

theorem tailTrace_4788644 : CollatzResearch.WordTrace tailWord_4788644 prefixEnd_4788644 2458876055268867642027433 := by
  unfold tailWord_4788644
  simp only [CollatzResearch.WordTrace]
  refine ⟨87328097631784049064558493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116437463509045398752744657 87328097631784049064558493)
  ·
    refine ⟨32748036611919018399209435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87328097631784049064558493 32748036611919018399209435)
    ·
      refine ⟨49122054917878527598814153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32748036611919018399209435 49122054917878527598814153)
      ·
        refine ⟨36841541188408895699110615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49122054917878527598814153 36841541188408895699110615)
        ·
          refine ⟨55262311782613343548665923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36841541188408895699110615 55262311782613343548665923)
          ·
            refine ⟨82893467673920015322998885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55262311782613343548665923 82893467673920015322998885)
            ·
              refine ⟨15542525188860002873062291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82893467673920015322998885 15542525188860002873062291)
              ·
                refine ⟨23313787783290004309593437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15542525188860002873062291 23313787783290004309593437)
                ·
                  refine ⟨8742670418733751616097539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23313787783290004309593437 8742670418733751616097539)
                  ·
                    refine ⟨13114005628100627424146309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8742670418733751616097539 13114005628100627424146309)
                    ·
                      refine ⟨2458876055268867642027433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13114005628100627424146309 2458876055268867642027433)
                      ·
                        rfl

theorem cell23_4788644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_4788644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788644 prefixEnd_4788644 := by exact prefixLift 4788644
  have htrace : WordTrace (prefixWord ++ tailWord_4788644) baseStart_4788644 baseEnd_4788644 := by
    simpa [prefixWord, tailWord_4788644, baseEnd_4788644] using wordTrace_append hprefix tailTrace_4788644
  have hstable : (prefixWord ++ tailWord_4788644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788644).length < 2 ^ (prefixWord ++ tailWord_4788644).sum := by decide
  have hdescent : baseEnd_4788644 < baseStart_4788644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788648 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4788648 : Nat := 118140960795 + 4788648 * 2 ^ 59
def prefixEnd_4788648 : Nat := 4983230072969 + 3 ^ 40 * 4788648 * 2
def baseEnd_4788648 : Nat := 2458878109191485626377415

theorem tailTrace_4788648 : CollatzResearch.WordTrace tailWord_4788648 prefixEnd_4788648 2458878109191485626377415 := by
  unfold tailWord_4788648
  simp only [CollatzResearch.WordTrace]
  refine ⟨87328170577776803406131299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116437560770369071208175065 87328170577776803406131299)
  ·
    refine ⟨130992255866665205109196949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87328170577776803406131299 130992255866665205109196949)
    ·
      refine ⟨6140261993749931489493607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130992255866665205109196949 6140261993749931489493607)
      ·
        refine ⟨9210392990624897234240411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6140261993749931489493607 9210392990624897234240411)
        ·
          refine ⟨13815589485937345851360617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9210392990624897234240411 13815589485937345851360617)
          ·
            refine ⟨10361692114453009388520463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13815589485937345851360617 10361692114453009388520463)
            ·
              refine ⟨15542538171679514082780695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10361692114453009388520463 15542538171679514082780695)
              ·
                refine ⟨23313807257519271124171043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15542538171679514082780695 23313807257519271124171043)
                ·
                  refine ⟨34970710886278906686256565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23313807257519271124171043 34970710886278906686256565)
                  ·
                    refine ⟨3278504145588647501836553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34970710886278906686256565 3278504145588647501836553)
                    ·
                      refine ⟨2458878109191485626377415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278504145588647501836553 2458878109191485626377415)
                      ·
                        rfl

theorem cell23_4788648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4788648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788648 prefixEnd_4788648 := by exact prefixLift 4788648
  have htrace : WordTrace (prefixWord ++ tailWord_4788648) baseStart_4788648 baseEnd_4788648 := by
    simpa [prefixWord, tailWord_4788648, baseEnd_4788648] using wordTrace_append hprefix tailTrace_4788648
  have hstable : (prefixWord ++ tailWord_4788648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788648).length < 2 ^ (prefixWord ++ tailWord_4788648).sum := by decide
  have hdescent : baseEnd_4788648 < baseStart_4788648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788706 : List Nat := [3, 3, 3, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4788706 : Nat := 118140960795 + 4788706 * 2 ^ 59
def prefixEnd_4788706 : Nat := 4983230072969 + 3 ^ 40 * 4788706 * 2
def baseEnd_4788706 : Nat := 2458907891069446399452149

theorem tailTrace_4788706 : CollatzResearch.WordTrace tailWord_4788706 prefixEnd_4788706 2458907891069446399452149 := by
  unfold tailWord_4788706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43664614147335870679468493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116438971059562321811915981 43664614147335870679468493)
  ·
    refine ⟨16374230305250951504800685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43664614147335870679468493 16374230305250951504800685)
    ·
      refine ⟨6140336364469106814300257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16374230305250951504800685 6140336364469106814300257)
      ·
        refine ⟨4605252273351830110725193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6140336364469106814300257 4605252273351830110725193)
        ·
          refine ⟨3453939205013872583043895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4605252273351830110725193 3453939205013872583043895)
          ·
            refine ⟨5180908807520808874565843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453939205013872583043895 5180908807520808874565843)
            ·
              refine ⟨7771363211281213311848765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180908807520808874565843 7771363211281213311848765)
              ·
                refine ⟨2914261204230454991943287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7771363211281213311848765 2914261204230454991943287)
                ·
                  refine ⟨4371391806345682487914931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2914261204230454991943287 4371391806345682487914931)
                  ·
                    refine ⟨6557087709518523731872397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4371391806345682487914931 6557087709518523731872397)
                    ·
                      refine ⟨2458907891069446399452149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6557087709518523731872397 2458907891069446399452149)
                      ·
                        rfl

theorem cell23_4788706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4788706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788706 prefixEnd_4788706 := by exact prefixLift 4788706
  have htrace : WordTrace (prefixWord ++ tailWord_4788706) baseStart_4788706 baseEnd_4788706 := by
    simpa [prefixWord, tailWord_4788706, baseEnd_4788706] using wordTrace_append hprefix tailTrace_4788706
  have hstable : (prefixWord ++ tailWord_4788706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788706).length < 2 ^ (prefixWord ++ tailWord_4788706).sum := by decide
  have hdescent : baseEnd_4788706 < baseStart_4788706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788711 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_4788711 : Nat := 118140960795 + 4788711 * 2 ^ 59
def prefixEnd_4788711 : Nat := 4983230072969 + 3 ^ 40 * 4788711 * 2
def baseEnd_4788711 : Nat := 2458910458472718879889625

theorem tailTrace_4788711 : CollatzResearch.WordTrace tailWord_4788711 prefixEnd_4788711 2458910458472718879889625 := by
  unfold tailWord_4788711
  simp only [CollatzResearch.WordTrace]
  refine ⟨174658638954325368571805987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116439092636216912381203991 174658638954325368571805987)
  ·
    refine ⟨261987958431488052857708981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174658638954325368571805987 261987958431488052857708981)
    ·
      refine ⟨24561371102952004955410217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261987958431488052857708981 24561371102952004955410217)
      ·
        refine ⟨18421028327214003716557663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24561371102952004955410217 18421028327214003716557663)
        ·
          refine ⟨27631542490821005574836495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18421028327214003716557663 27631542490821005574836495)
          ·
            refine ⟨41447313736231508362254743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27631542490821005574836495 41447313736231508362254743)
            ·
              refine ⟨62170970604347262543382115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41447313736231508362254743 62170970604347262543382115)
              ·
                refine ⟨93256455906520893815073173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62170970604347262543382115 93256455906520893815073173)
                ·
                  refine ⟨4371396370618166897581555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93256455906520893815073173 4371396370618166897581555)
                  ·
                    refine ⟨6557094555927250346372333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4371396370618166897581555 6557094555927250346372333)
                    ·
                      refine ⟨2458910458472718879889625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6557094555927250346372333 2458910458472718879889625)
                      ·
                        rfl

theorem cell23_4788711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_4788711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788711 prefixEnd_4788711 := by exact prefixLift 4788711
  have htrace : WordTrace (prefixWord ++ tailWord_4788711) baseStart_4788711 baseEnd_4788711 := by
    simpa [prefixWord, tailWord_4788711, baseEnd_4788711] using wordTrace_append hprefix tailTrace_4788711
  have hstable : (prefixWord ++ tailWord_4788711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788711).length < 2 ^ (prefixWord ++ tailWord_4788711).sum := by decide
  have hdescent : baseEnd_4788711 < baseStart_4788711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788712 : List Nat := [2, 1, 4, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_4788712 : Nat := 118140960795 + 4788712 * 2 ^ 59
def prefixEnd_4788712 : Nat := 4983230072969 + 3 ^ 40 * 4788712 * 2
def baseEnd_4788712 : Nat := 2458910971953373375977121

theorem tailTrace_4788712 : CollatzResearch.WordTrace tailWord_4788712 prefixEnd_4788712 2458910971953373375977121 := by
  unfold tailWord_4788712
  simp only [CollatzResearch.WordTrace]
  refine ⟨87329337713660872871296195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116439116951547830495061593 87329337713660872871296195)
  ·
    refine ⟨130994006570491309306944293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87329337713660872871296195 130994006570491309306944293)
    ·
      refine ⟨24561376231967120495052055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130994006570491309306944293 24561376231967120495052055)
      ·
        refine ⟨36842064347950680742578083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24561376231967120495052055 36842064347950680742578083)
        ·
          refine ⟨55263096521926021113867125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36842064347950680742578083 55263096521926021113867125)
          ·
            refine ⟨5180915298930564479425043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55263096521926021113867125 5180915298930564479425043)
            ·
              refine ⟨7771372948395846719137565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180915298930564479425043 7771372948395846719137565)
              ·
                refine ⟨2914264855648442519676587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7771372948395846719137565 2914264855648442519676587)
                ·
                  refine ⟨4371397283472663779514881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2914264855648442519676587 4371397283472663779514881)
                  ·
                    refine ⟨3278547962604497834636161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4371397283472663779514881 3278547962604497834636161)
                    ·
                      refine ⟨2458910971953373375977121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278547962604497834636161 2458910971953373375977121)
                      ·
                        rfl

theorem cell23_4788712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_4788712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788712 prefixEnd_4788712 := by exact prefixLift 4788712
  have htrace : WordTrace (prefixWord ++ tailWord_4788712) baseStart_4788712 baseEnd_4788712 := by
    simpa [prefixWord, tailWord_4788712, baseEnd_4788712] using wordTrace_append hprefix tailTrace_4788712
  have hstable : (prefixWord ++ tailWord_4788712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788712).length < 2 ^ (prefixWord ++ tailWord_4788712).sum := by decide
  have hdescent : baseEnd_4788712 < baseStart_4788712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788791 : List Nat := [1, 1, 3, 1, 2, 3, 3, 4, 5]
def baseStart_4788791 : Nat := 118140960795 + 4788791 * 2 ^ 59
def prefixEnd_4788791 : Nat := 4983230072969 + 3 ^ 40 * 4788791 * 2
def baseEnd_4788791 : Nat := 273216837436119840765473

theorem tailTrace_4788791 : CollatzResearch.WordTrace tailWord_4788791 prefixEnd_4788791 273216837436119840765473 := by
  unfold tailWord_4788791
  simp only [CollatzResearch.WordTrace]
  refine ⟨174661556794035542234718227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116441037862690361489812151 174661556794035542234718227)
  ·
    refine ⟨261992335191053313352077341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174661556794035542234718227 261992335191053313352077341)
    ·
      refine ⟨98247125696644992507029003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261992335191053313352077341 98247125696644992507029003)
      ·
        refine ⟨147370688544967488760543505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98247125696644992507029003 147370688544967488760543505)
        ·
          refine ⟨110528016408725616570407629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147370688544967488760543505 110528016408725616570407629)
          ·
            refine ⟨41448006153272106213902861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110528016408725616570407629 41448006153272106213902861)
            ·
              refine ⟨15543002307477039830213573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41448006153272106213902861 15543002307477039830213573)
              ·
                refine ⟨2914312932651944968165045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15543002307477039830213573 2914312932651944968165045)
                ·
                  refine ⟨273216837436119840765473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2914312932651944968165045 273216837436119840765473)
                  ·
                    rfl

theorem cell23_4788791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 5].length) (baseStart_4788791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788791 prefixEnd_4788791 := by exact prefixLift 4788791
  have htrace : WordTrace (prefixWord ++ tailWord_4788791) baseStart_4788791 baseEnd_4788791 := by
    simpa [prefixWord, tailWord_4788791, baseEnd_4788791] using wordTrace_append hprefix tailTrace_4788791
  have hstable : (prefixWord ++ tailWord_4788791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788791).length < 2 ^ (prefixWord ++ tailWord_4788791).sum := by decide
  have hdescent : baseEnd_4788791 < baseStart_4788791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788801 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_4788801 : Nat := 118140960795 + 4788801 * 2 ^ 59
def prefixEnd_4788801 : Nat := 4983230072969 + 3 ^ 40 * 4788801 * 2
def baseEnd_4788801 : Nat := 2458956671731623527764211

theorem tailTrace_4788801 : CollatzResearch.WordTrace tailWord_4788801 prefixEnd_4788801 2458956671731623527764211 := by
  unfold tailWord_4788801
  simp only [CollatzResearch.WordTrace]
  refine ⟨174661921523999313942582257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116441281015999542628388171 174661921523999313942582257)
  ·
    refine ⟨130996441142999485456936693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174661921523999313942582257 130996441142999485456936693)
    ·
      refine ⟨12280916357156201761587815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130996441142999485456936693 12280916357156201761587815)
      ·
        refine ⟨18421374535734302642381723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12280916357156201761587815 18421374535734302642381723)
        ·
          refine ⟨27632061803601453963572585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18421374535734302642381723 27632061803601453963572585)
          ·
            refine ⟨20724046352701090472679439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27632061803601453963572585 20724046352701090472679439)
            ·
              refine ⟨31086069529051635709019159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20724046352701090472679439 31086069529051635709019159)
              ·
                refine ⟨46629104293577453563528739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31086069529051635709019159 46629104293577453563528739)
                ·
                  refine ⟨69943656440366180345293109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46629104293577453563528739 69943656440366180345293109)
                  ·
                    refine ⟨6557217791284329407371229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69943656440366180345293109 6557217791284329407371229)
                    ·
                      refine ⟨2458956671731623527764211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6557217791284329407371229 2458956671731623527764211)
                      ·
                        rfl

theorem cell23_4788801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_4788801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788801 prefixEnd_4788801 := by exact prefixLift 4788801
  have htrace : WordTrace (prefixWord ++ tailWord_4788801) baseStart_4788801 baseEnd_4788801 := by
    simpa [prefixWord, tailWord_4788801, baseEnd_4788801] using wordTrace_append hprefix tailTrace_4788801
  have hstable : (prefixWord ++ tailWord_4788801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788801).length < 2 ^ (prefixWord ++ tailWord_4788801).sum := by decide
  have hdescent : baseEnd_4788801 < baseStart_4788801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788814 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_4788814 : Nat := 118140960795 + 4788814 * 2 ^ 59
def prefixEnd_4788814 : Nat := 4983230072969 + 3 ^ 40 * 4788814 * 2
def baseEnd_4788814 : Nat := 2458963346980131976901651

theorem tailTrace_4788814 : CollatzResearch.WordTrace tailWord_4788814 prefixEnd_4788814 2458963346980131976901651 := by
  unfold tailWord_4788814
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832799459119027145350687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116441597115301478108536997 21832799459119027145350687)
  ·
    refine ⟨32749199188678540718026031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21832799459119027145350687 32749199188678540718026031)
    ·
      refine ⟨49123798783017811077039047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32749199188678540718026031 49123798783017811077039047)
      ·
        refine ⟨73685698174526716615558571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49123798783017811077039047 73685698174526716615558571)
        ·
          refine ⟨110528547261790074923337857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73685698174526716615558571 110528547261790074923337857)
          ·
            refine ⟨82896410446342556192503393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110528547261790074923337857 82896410446342556192503393)
            ·
              refine ⟨62172307834756917144377545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82896410446342556192503393 62172307834756917144377545)
              ·
                refine ⟨46629230876067687858283159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62172307834756917144377545 46629230876067687858283159)
                ·
                  refine ⟨69943846314101531787424739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46629230876067687858283159 69943846314101531787424739)
                  ·
                    refine ⟨104915769471152297681137109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69943846314101531787424739 104915769471152297681137109)
                    ·
                      refine ⟨2458963346980131976901651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104915769471152297681137109 2458963346980131976901651)
                      ·
                        rfl

theorem cell23_4788814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_4788814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788814 prefixEnd_4788814 := by exact prefixLift 4788814
  have htrace : WordTrace (prefixWord ++ tailWord_4788814) baseStart_4788814 baseEnd_4788814 := by
    simpa [prefixWord, tailWord_4788814, baseEnd_4788814] using wordTrace_append hprefix tailTrace_4788814
  have hstable : (prefixWord ++ tailWord_4788814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788814).length < 2 ^ (prefixWord ++ tailWord_4788814).sum := by decide
  have hdescent : baseEnd_4788814 < baseStart_4788814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788821 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_4788821 : Nat := 118140960795 + 4788821 * 2 ^ 59
def prefixEnd_4788821 : Nat := 4983230072969 + 3 ^ 40 * 4788821 * 2
def baseEnd_4788821 : Nat := 819655647114904483171373

theorem tailTrace_4788821 : CollatzResearch.WordTrace tailWord_4788821 prefixEnd_4788821 819655647114904483171373 := by
  unfold tailWord_4788821
  simp only [CollatzResearch.WordTrace]
  refine ⟨174662650983926857358310317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116441767322617904905540211 174662650983926857358310317)
  ·
    refine ⟨65498494118972571509366369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174662650983926857358310317 65498494118972571509366369)
    ·
      refine ⟨49123870589229428632024777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65498494118972571509366369 49123870589229428632024777)
      ·
        refine ⟨36842902941922071474018583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49123870589229428632024777 36842902941922071474018583)
        ·
          refine ⟨55264354412883107211027875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36842902941922071474018583 55264354412883107211027875)
          ·
            refine ⟨82896531619324660816541813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55264354412883107211027875 82896531619324660816541813)
            ·
              refine ⟨7771549839311686951550795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82896531619324660816541813 7771549839311686951550795)
              ·
                refine ⟨11657324758967530427326193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7771549839311686951550795 11657324758967530427326193)
                ·
                  refine ⟨8742993569225647820494645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11657324758967530427326193 8742993569225647820494645)
                  ·
                    refine ⟨819655647114904483171373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8742993569225647820494645 819655647114904483171373)
                    ·
                      rfl

theorem cell23_4788821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_4788821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788821 prefixEnd_4788821 := by exact prefixLift 4788821
  have htrace : WordTrace (prefixWord ++ tailWord_4788821) baseStart_4788821 baseEnd_4788821 := by
    simpa [prefixWord, tailWord_4788821, baseEnd_4788821] using wordTrace_append hprefix tailTrace_4788821
  have hstable : (prefixWord ++ tailWord_4788821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788821).length < 2 ^ (prefixWord ++ tailWord_4788821).sum := by decide
  have hdescent : baseEnd_4788821 < baseStart_4788821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788844 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_4788844 : Nat := 118140960795 + 4788844 * 2 ^ 59
def prefixEnd_4788844 : Nat := 4983230072969 + 3 ^ 40 * 4788844 * 2
def baseEnd_4788844 : Nat := 2458978751399766859526513

theorem tailTrace_4788844 : CollatzResearch.WordTrace tailWord_4788844 prefixEnd_4788844 2458978751399766859526513 := by
  unfold tailWord_4788844
  simp only [CollatzResearch.WordTrace]
  refine ⟨87331744931421766143198793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116442326575229021524265057 87331744931421766143198793)
  ·
    refine ⟨65498808698566324607399095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87331744931421766143198793 65498808698566324607399095)
    ·
      refine ⟨98248213047849486911098643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65498808698566324607399095 98248213047849486911098643)
      ·
        refine ⟨147372319571774230366647965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98248213047849486911098643 147372319571774230366647965)
        ·
          refine ⟨55264619839415336387492987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147372319571774230366647965 55264619839415336387492987)
          ·
            refine ⟨82896929759123004581239481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55264619839415336387492987 82896929759123004581239481)
            ·
              refine ⟨62172697319342253435929611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82896929759123004581239481 62172697319342253435929611)
              ·
                refine ⟨93259045979013380153894417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62172697319342253435929611 93259045979013380153894417)
                ·
                  refine ⟨69944284484260035115420813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93259045979013380153894417 69944284484260035115420813)
                  ·
                    refine ⟨26229106681597513168282805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69944284484260035115420813 26229106681597513168282805)
                    ·
                      refine ⟨2458978751399766859526513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26229106681597513168282805 2458978751399766859526513)
                      ·
                        rfl

theorem cell23_4788844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_4788844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788844 prefixEnd_4788844 := by exact prefixLift 4788844
  have htrace : WordTrace (prefixWord ++ tailWord_4788844) baseStart_4788844 baseEnd_4788844 := by
    simpa [prefixWord, tailWord_4788844, baseEnd_4788844] using wordTrace_append hprefix tailTrace_4788844
  have hstable : (prefixWord ++ tailWord_4788844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788844).length < 2 ^ (prefixWord ++ tailWord_4788844).sum := by decide
  have hdescent : baseEnd_4788844 < baseStart_4788844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788868 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_4788868 : Nat := 118140960795 + 4788868 * 2 ^ 59
def prefixEnd_4788868 : Nat := 4983230072969 + 3 ^ 40 * 4788868 * 2
def baseEnd_4788868 : Nat := 819663691645158255208801

theorem tailTrace_4788868 : CollatzResearch.WordTrace tailWord_4788868 prefixEnd_4788868 819663691645158255208801 := by
  unfold tailWord_4788868
  simp only [CollatzResearch.WordTrace]
  refine ⟨87332182607378292192635629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116442910143171056256847505 87332182607378292192635629)
  ·
    refine ⟨32749568477766859572238361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87332182607378292192635629 32749568477766859572238361)
    ·
      refine ⟨24562176358325144679178771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32749568477766859572238361 24562176358325144679178771)
      ·
        refine ⟨36843264537487717018768157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24562176358325144679178771 36843264537487717018768157)
        ·
          refine ⟨13816224201557893882038059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36843264537487717018768157 13816224201557893882038059)
          ·
            refine ⟨20724336302336840823057089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13816224201557893882038059 20724336302336840823057089)
            ·
              refine ⟨15543252226752630617292817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20724336302336840823057089 15543252226752630617292817)
              ·
                refine ⟨11657439170064472962969613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15543252226752630617292817 11657439170064472962969613)
                ·
                  refine ⟨4371539688774177361113605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11657439170064472962969613 4371539688774177361113605)
                  ·
                    refine ⟨819663691645158255208801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4371539688774177361113605 819663691645158255208801)
                    ·
                      rfl

theorem cell23_4788868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_4788868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788868 prefixEnd_4788868 := by exact prefixLift 4788868
  have htrace : WordTrace (prefixWord ++ tailWord_4788868) baseStart_4788868 baseEnd_4788868 := by
    simpa [prefixWord, tailWord_4788868, baseEnd_4788868] using wordTrace_append hprefix tailTrace_4788868
  have hstable : (prefixWord ++ tailWord_4788868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788868).length < 2 ^ (prefixWord ++ tailWord_4788868).sum := by decide
  have hdescent : baseEnd_4788868 < baseStart_4788868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788878 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4788878 : Nat := 118140960795 + 4788878 * 2 ^ 59
def prefixEnd_4788878 : Nat := 4983230072969 + 3 ^ 40 * 4788878 * 2
def baseEnd_4788878 : Nat := 2458996209742019726501357

theorem tailTrace_4788878 : CollatzResearch.WordTrace tailWord_4788878 prefixEnd_4788878 2458996209742019726501357 := by
  unfold tailWord_4788878
  simp only [CollatzResearch.WordTrace]
  refine ⟨21833091243090044511641911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116443153296480237395423525 21833091243090044511641911)
  ·
    refine ⟨32749636864635066767462867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21833091243090044511641911 32749636864635066767462867)
    ·
      refine ⟨49124455296952600151194301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32749636864635066767462867 49124455296952600151194301)
      ·
        refine ⟨18421670736357225056697863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49124455296952600151194301 18421670736357225056697863)
        ·
          refine ⟨27632506104535837585046795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18421670736357225056697863 27632506104535837585046795)
          ·
            refine ⟨41448759156803756377570193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27632506104535837585046795 41448759156803756377570193)
            ·
              refine ⟨31086569367602817283177645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41448759156803756377570193 31086569367602817283177645)
              ·
                refine ⟨11657463512851056481191617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31086569367602817283177645 11657463512851056481191617)
                ·
                  refine ⟨8743097634638292360893713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11657463512851056481191617 8743097634638292360893713)
                  ·
                    refine ⟨6557323225978719270670285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8743097634638292360893713 6557323225978719270670285)
                    ·
                      refine ⟨2458996209742019726501357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6557323225978719270670285 2458996209742019726501357)
                      ·
                        rfl

theorem cell23_4788878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4788878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788878 prefixEnd_4788878 := by exact prefixLift 4788878
  have htrace : WordTrace (prefixWord ++ tailWord_4788878) baseStart_4788878 baseEnd_4788878 := by
    simpa [prefixWord, tailWord_4788878, baseEnd_4788878] using wordTrace_append hprefix tailTrace_4788878
  have hstable : (prefixWord ++ tailWord_4788878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788878).length < 2 ^ (prefixWord ++ tailWord_4788878).sum := by decide
  have hdescent : baseEnd_4788878 < baseStart_4788878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788928 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 1, 5]
def baseStart_4788928 : Nat := 118140960795 + 4788928 * 2 ^ 59
def prefixEnd_4788928 : Nat := 4983230072969 + 3 ^ 40 * 4788928 * 2
def baseEnd_4788928 : Nat := 819673961258248176958709

theorem tailTrace_4788928 : CollatzResearch.WordTrace tailWord_4788928 prefixEnd_4788928 819673961258248176958709 := by
  unfold tailWord_4788928
  simp only [CollatzResearch.WordTrace]
  refine ⟨87333276797269607316227719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116444369063026143088303625 87333276797269607316227719)
  ·
    refine ⟨130999915195904410974341579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87333276797269607316227719 130999915195904410974341579)
    ·
      refine ⟨196499872793856616461512369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130999915195904410974341579 196499872793856616461512369)
      ·
        refine ⟨147374904595392462346134277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196499872793856616461512369 147374904595392462346134277)
        ·
          refine ⟨27632794611636086689900177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147374904595392462346134277 27632794611636086689900177)
          ·
            refine ⟨20724595958727065017425133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27632794611636086689900177 20724595958727065017425133)
            ·
              refine ⟨7771723484522649381534425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20724595958727065017425133 7771723484522649381534425)
              ·
                refine ⟨5828792613391987036150819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7771723484522649381534425 5828792613391987036150819)
                ·
                  refine ⟨8743188920087980554226229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5828792613391987036150819 8743188920087980554226229)
                  ·
                    refine ⟨819673961258248176958709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8743188920087980554226229 819673961258248176958709)
                    ·
                      rfl

theorem cell23_4788928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_4788928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788928 prefixEnd_4788928 := by exact prefixLift 4788928
  have htrace : WordTrace (prefixWord ++ tailWord_4788928) baseStart_4788928 baseEnd_4788928 := by
    simpa [prefixWord, tailWord_4788928, baseEnd_4788928] using wordTrace_append hprefix tailTrace_4788928
  have hstable : (prefixWord ++ tailWord_4788928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788928).length < 2 ^ (prefixWord ++ tailWord_4788928).sum := by decide
  have hdescent : baseEnd_4788928 < baseStart_4788928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788959 : List Nat := [1, 1, 2, 3, 2, 5, 2, 2, 1, 1, 3]
def baseStart_4788959 : Nat := 118140960795 + 4788959 * 2 ^ 59
def prefixEnd_4788959 : Nat := 4983230072969 + 3 ^ 40 * 4788959 * 2
def baseEnd_4788959 : Nat := 2459037801675033909588485

theorem tailTrace_4788959 : CollatzResearch.WordTrace tailWord_4788959 prefixEnd_4788959 2459037801675033909588485 := by
  unfold tailWord_4788959
  simp only [CollatzResearch.WordTrace]
  refine ⟨174667684257426906926833931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116445122838284604617889287 174667684257426906926833931)
  ·
    refine ⟨262001526386140360390250897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174667684257426906926833931 262001526386140360390250897)
    ·
      refine ⟨196501144789605270292688173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262001526386140360390250897 196501144789605270292688173)
      ·
        refine ⟨73687929296101976359758065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196501144789605270292688173 73687929296101976359758065)
        ·
          refine ⟨55265946972076482269818549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73687929296101976359758065 55265946972076482269818549)
          ·
            refine ⟨5181182528632170212795489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55265946972076482269818549 5181182528632170212795489)
            ·
              refine ⟨3885886896474127659596617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5181182528632170212795489 3885886896474127659596617)
              ·
                refine ⟨2914415172355595744697463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3885886896474127659596617 2914415172355595744697463)
                ·
                  refine ⟨4371622758533393617046195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2914415172355595744697463 4371622758533393617046195)
                  ·
                    refine ⟨6557434137800090425569293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4371622758533393617046195 6557434137800090425569293)
                    ·
                      refine ⟨2459037801675033909588485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6557434137800090425569293 2459037801675033909588485)
                      ·
                        rfl

theorem cell23_4788959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_4788959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788959 prefixEnd_4788959 := by exact prefixLift 4788959
  have htrace : WordTrace (prefixWord ++ tailWord_4788959) baseStart_4788959 baseEnd_4788959 := by
    simpa [prefixWord, tailWord_4788959, baseEnd_4788959] using wordTrace_append hprefix tailTrace_4788959
  have hstable : (prefixWord ++ tailWord_4788959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788959).length < 2 ^ (prefixWord ++ tailWord_4788959).sum := by decide
  have hdescent : baseEnd_4788959 < baseStart_4788959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788978 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4788978 : Nat := 118140960795 + 4788978 * 2 ^ 59
def prefixEnd_4788978 : Nat := 4983230072969 + 3 ^ 40 * 4788978 * 2
def baseEnd_4788978 : Nat := 2459047557807469335250897

theorem tailTrace_4788978 : CollatzResearch.WordTrace tailWord_4788978 prefixEnd_4788978 2459047557807469335250897 := by
  unfold tailWord_4788978
  simp only [CollatzResearch.WordTrace]
  refine ⟨43667094311089518292943897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116445584829572048781183725 43667094311089518292943897)
  ·
    refine ⟨32750320733317138719707923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43667094311089518292943897 32750320733317138719707923)
    ·
      refine ⟨49125481099975708079561885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32750320733317138719707923 49125481099975708079561885)
      ·
        refine ⟨18422055412490890529835707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49125481099975708079561885 18422055412490890529835707)
        ·
          refine ⟨27633083118736335794753561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18422055412490890529835707 27633083118736335794753561)
          ·
            refine ⟨20724812339052251846065171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27633083118736335794753561 20724812339052251846065171)
            ·
              refine ⟨31087218508578377769097757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20724812339052251846065171 31087218508578377769097757)
              ·
                refine ⟨11657706940716891663411659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31087218508578377769097757 11657706940716891663411659)
                ·
                  refine ⟨17486560411075337495117489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11657706940716891663411659 17486560411075337495117489)
                  ·
                    refine ⟨13114920308306503121338117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17486560411075337495117489 13114920308306503121338117)
                    ·
                      refine ⟨2459047557807469335250897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13114920308306503121338117 2459047557807469335250897)
                      ·
                        rfl

theorem cell23_4788978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4788978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788978 prefixEnd_4788978 := by exact prefixLift 4788978
  have htrace : WordTrace (prefixWord ++ tailWord_4788978) baseStart_4788978 baseEnd_4788978 := by
    simpa [prefixWord, tailWord_4788978, baseEnd_4788978] using wordTrace_append hprefix tailTrace_4788978
  have hstable : (prefixWord ++ tailWord_4788978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788978).length < 2 ^ (prefixWord ++ tailWord_4788978).sum := by decide
  have hdescent : baseEnd_4788978 < baseStart_4788978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788982 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_4788982 : Nat := 118140960795 + 4788982 * 2 ^ 59
def prefixEnd_4788982 : Nat := 4983230072969 + 3 ^ 40 * 4788982 * 2
def baseEnd_4788982 : Nat := 2459049611730087319600879

theorem tailTrace_4788982 : CollatzResearch.WordTrace tailWord_4788982 prefixEnd_4788982 2459049611730087319600879 := by
  unfold tailWord_4788982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10916782696021473865932575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116445682090895721236614133 10916782696021473865932575)
  ·
    refine ⟨16375174044032210798898863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10916782696021473865932575 16375174044032210798898863)
    ·
      refine ⟨24562761066048316198348295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16375174044032210798898863 24562761066048316198348295)
      ·
        refine ⟨36844141599072474297522443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24562761066048316198348295 36844141599072474297522443)
        ·
          refine ⟨55266212398608711446283665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36844141599072474297522443 55266212398608711446283665)
          ·
            refine ⟨41449659298956533584712749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55266212398608711446283665 41449659298956533584712749)
            ·
              refine ⟨15543622237108700094267281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41449659298956533584712749 15543622237108700094267281)
              ·
                refine ⟨11657716677831525070700461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15543622237108700094267281 11657716677831525070700461)
                ·
                  refine ⟨4371643754186821901512673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11657716677831525070700461 4371643754186821901512673)
                  ·
                    refine ⟨3278732815640116426134505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4371643754186821901512673 3278732815640116426134505)
                    ·
                      refine ⟨2459049611730087319600879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278732815640116426134505 2459049611730087319600879)
                      ·
                        rfl

theorem cell23_4788982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_4788982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788982 prefixEnd_4788982 := by exact prefixLift 4788982
  have htrace : WordTrace (prefixWord ++ tailWord_4788982) baseStart_4788982 baseEnd_4788982 := by
    simpa [prefixWord, tailWord_4788982, baseEnd_4788982] using wordTrace_append hprefix tailTrace_4788982
  have hstable : (prefixWord ++ tailWord_4788982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788982).length < 2 ^ (prefixWord ++ tailWord_4788982).sum := by decide
  have hdescent : baseEnd_4788982 < baseStart_4788982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788988 : List Nat := [2, 2, 2, 1, 3, 3, 3, 7]
def baseStart_4788988 : Nat := 118140960795 + 4788988 * 2 ^ 59
def prefixEnd_4788988 : Nat := 4983230072969 + 3 ^ 40 * 4788988 * 2
def baseEnd_4788988 : Nat := 91076025652370899856513

theorem tailTrace_4788988 : CollatzResearch.WordTrace tailWord_4788988 prefixEnd_4788988 91076025652370899856513 := by
  unfold tailWord_4788988
  simp only [CollatzResearch.WordTrace]
  refine ⟨87334370987160922439819809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116445827982881229919759745 87334370987160922439819809)
  ·
    refine ⟨65500778240370691829864857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87334370987160922439819809 65500778240370691829864857)
    ·
      refine ⟨49125583680278018872398643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65500778240370691829864857 49125583680278018872398643)
      ·
        refine ⟨73688375520417028308597965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49125583680278018872398643 73688375520417028308597965)
        ·
          refine ⟨27633140820156385615724237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73688375520417028308597965 27633140820156385615724237)
          ·
            refine ⟨10362427807558644605896589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27633140820156385615724237 10362427807558644605896589)
            ·
              refine ⟨3885910427834491727211221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10362427807558644605896589 3885910427834491727211221)
              ·
                refine ⟨91076025652370899856513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3885910427834491727211221 91076025652370899856513)
                ·
                  rfl

theorem cell23_4788988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 7].length) (baseStart_4788988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788988 prefixEnd_4788988 := by exact prefixLift 4788988
  have htrace : WordTrace (prefixWord ++ tailWord_4788988) baseStart_4788988 baseEnd_4788988 := by
    simpa [prefixWord, tailWord_4788988, baseEnd_4788988] using wordTrace_append hprefix tailTrace_4788988
  have hstable : (prefixWord ++ tailWord_4788988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788988).length < 2 ^ (prefixWord ++ tailWord_4788988).sum := by decide
  have hdescent : baseEnd_4788988 < baseStart_4788988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4788999 : List Nat := [1, 1, 4, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4788999 : Nat := 118140960795 + 4788999 * 2 ^ 59
def prefixEnd_4788999 : Nat := 4983230072969 + 3 ^ 40 * 4788999 * 2
def baseEnd_4788999 : Nat := 2459058340901213753088301

theorem tailTrace_4788999 : CollatzResearch.WordTrace tailWord_4788999 prefixEnd_4788999 2459058340901213753088301 := by
  unfold tailWord_4788999
  simp only [CollatzResearch.WordTrace]
  refine ⟨174669143177281993758290051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116446095451521329172193367 174669143177281993758290051)
  ·
    refine ⟨262003714765922990637435077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174669143177281993758290051 262003714765922990637435077)
    ·
      refine ⟨49125696518610560744519077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262003714765922990637435077 49125696518610560744519077)
      ·
        refine ⟨9211068097239480139597327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49125696518610560744519077 9211068097239480139597327)
        ·
          refine ⟨13816602145859220209395991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9211068097239480139597327 13816602145859220209395991)
          ·
            refine ⟨20724903218788830314093987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13816602145859220209395991 20724903218788830314093987)
            ·
              refine ⟨31087354828183245471140981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20724903218788830314093987 31087354828183245471140981)
              ·
                refine ⟨2914439515142179262919467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31087354828183245471140981 2914439515142179262919467)
                ·
                  refine ⟨4371659272713268894379201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2914439515142179262919467 4371659272713268894379201)
                  ·
                    refine ⟨3278744454534951670784401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4371659272713268894379201 3278744454534951670784401)
                    ·
                      refine ⟨2459058340901213753088301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278744454534951670784401 2459058340901213753088301)
                      ·
                        rfl

theorem cell23_4788999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4788999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4788999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4788999 prefixEnd_4788999 := by exact prefixLift 4788999
  have htrace : WordTrace (prefixWord ++ tailWord_4788999) baseStart_4788999 baseEnd_4788999 := by
    simpa [prefixWord, tailWord_4788999, baseEnd_4788999] using wordTrace_append hprefix tailTrace_4788999
  have hstable : (prefixWord ++ tailWord_4788999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4788999).length < 2 ^ (prefixWord ++ tailWord_4788999).sum := by decide
  have hdescent : baseEnd_4788999 < baseStart_4788999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4788999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789042 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_4789042 : Nat := 118140960795 + 4789042 * 2 ^ 59
def prefixEnd_4789042 : Nat := 4983230072969 + 3 ^ 40 * 4789042 * 2
def baseEnd_4789042 : Nat := 2459080420569357084850603

theorem tailTrace_4789042 : CollatzResearch.WordTrace tailWord_4789042 prefixEnd_4789042 2459080420569357084850603 := by
  unfold tailWord_4789042
  simp only [CollatzResearch.WordTrace]
  refine ⟨43667677879031553025526345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116447141010750808068070253 43667677879031553025526345)
  ·
    refine ⟨32750758409273664769144759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43667677879031553025526345 32750758409273664769144759)
    ·
      refine ⟨49126137613910497153717139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32750758409273664769144759 49126137613910497153717139)
      ·
        refine ⟨73689206420865745730575709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49126137613910497153717139 73689206420865745730575709)
        ·
          refine ⟨27633452407824654648965891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73689206420865745730575709 27633452407824654648965891)
          ·
            refine ⟨41450178611736981973448837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27633452407824654648965891 41450178611736981973448837)
            ·
              refine ⟨7771908489700684120021657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41450178611736981973448837 7771908489700684120021657)
              ·
                refine ⟨5828931367275513090016243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7771908489700684120021657 5828931367275513090016243)
                ·
                  refine ⟨8743397050913269635024365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5828931367275513090016243 8743397050913269635024365)
                  ·
                    refine ⟨3278773894092476113134137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8743397050913269635024365 3278773894092476113134137)
                    ·
                      refine ⟨2459080420569357084850603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278773894092476113134137 2459080420569357084850603)
                      ·
                        rfl

theorem cell23_4789042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_4789042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789042 prefixEnd_4789042 := by exact prefixLift 4789042
  have htrace : WordTrace (prefixWord ++ tailWord_4789042) baseStart_4789042 baseEnd_4789042 := by
    simpa [prefixWord, tailWord_4789042, baseEnd_4789042] using wordTrace_append hprefix tailTrace_4789042
  have hstable : (prefixWord ++ tailWord_4789042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789042).length < 2 ^ (prefixWord ++ tailWord_4789042).sum := by decide
  have hdescent : baseEnd_4789042 < baseStart_4789042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789088 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3]
def baseStart_4789088 : Nat := 118140960795 + 4789088 * 2 ^ 59
def prefixEnd_4789088 : Nat := 4983230072969 + 3 ^ 40 * 4789088 * 2
def baseEnd_4789088 : Nat := 2459104040679463904875391

theorem tailTrace_4789088 : CollatzResearch.WordTrace tailWord_4789088 prefixEnd_4789088 2459104040679463904875391 := by
  unfold tailWord_4789088
  simp only [CollatzResearch.WordTrace]
  refine ⟨87336194636979780979139959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116448259515973041305519945 87336194636979780979139959)
  ·
    refine ⟨131004291955469671468709939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87336194636979780979139959 131004291955469671468709939)
    ·
      refine ⟨196506437933204507203064909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131004291955469671468709939 196506437933204507203064909)
      ·
        refine ⟨73689914224951690201149341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196506437933204507203064909 73689914224951690201149341)
        ·
          refine ⟨27633717834356883825431003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73689914224951690201149341 27633717834356883825431003)
          ·
            refine ⟨41450576751535325738146505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27633717834356883825431003 41450576751535325738146505)
            ·
              refine ⟨31087932563651494303609879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41450576751535325738146505 31087932563651494303609879)
              ·
                refine ⟨46631898845477241455414819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31087932563651494303609879 46631898845477241455414819)
                ·
                  refine ⟨69947848268215862183122229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46631898845477241455414819 69947848268215862183122229)
                  ·
                    refine ⟨6557610775145237079667709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69947848268215862183122229 6557610775145237079667709)
                    ·
                      refine ⟨2459104040679463904875391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6557610775145237079667709 2459104040679463904875391)
                      ·
                        rfl

theorem cell23_4789088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_4789088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789088 prefixEnd_4789088 := by exact prefixLift 4789088
  have htrace : WordTrace (prefixWord ++ tailWord_4789088) baseStart_4789088 baseEnd_4789088 := by
    simpa [prefixWord, tailWord_4789088, baseEnd_4789088] using wordTrace_append hprefix tailTrace_4789088
  have hstable : (prefixWord ++ tailWord_4789088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789088).length < 2 ^ (prefixWord ++ tailWord_4789088).sum := by decide
  have hdescent : baseEnd_4789088 < baseStart_4789088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789159 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 2, 5]
def baseStart_4789159 : Nat := 118140960795 + 4789159 * 2 ^ 59
def prefixEnd_4789159 : Nat := 4983230072969 + 3 ^ 40 * 4789159 * 2
def baseEnd_4789159 : Nat := 819713499268644375695855

theorem tailTrace_4789159 : CollatzResearch.WordTrace tailWord_4789159 prefixEnd_4789159 819713499268644375695855 := by
  unfold tailWord_4789159
  simp only [CollatzResearch.WordTrace]
  refine ⟨174674978856702341084114531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116449985904468227389409687 174674978856702341084114531)
  ·
    refine ⟨262012468285053511626171797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174674978856702341084114531 262012468285053511626171797)
    ·
      refine ⟨12281834450861883357476803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 262012468285053511626171797 12281834450861883357476803)
      ·
        refine ⟨18422751676292825036215205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12281834450861883357476803 18422751676292825036215205)
        ·
          refine ⟨3454265939304904694290351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18422751676292825036215205 3454265939304904694290351)
          ·
            refine ⟨5181398908957357041435527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3454265939304904694290351 5181398908957357041435527)
            ·
              refine ⟨7772098363436035562153291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181398908957357041435527 7772098363436035562153291)
              ·
                refine ⟨11658147545154053343229937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7772098363436035562153291 11658147545154053343229937)
                ·
                  refine ⟨8743610658865540007422453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11658147545154053343229937 8743610658865540007422453)
                  ·
                    refine ⟨819713499268644375695855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8743610658865540007422453 819713499268644375695855)
                    ·
                      rfl

theorem cell23_4789159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_4789159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789159 prefixEnd_4789159 := by exact prefixLift 4789159
  have htrace : WordTrace (prefixWord ++ tailWord_4789159) baseStart_4789159 baseEnd_4789159 := by
    simpa [prefixWord, tailWord_4789159, baseEnd_4789159] using wordTrace_append hprefix tailTrace_4789159
  have hstable : (prefixWord ++ tailWord_4789159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789159).length < 2 ^ (prefixWord ++ tailWord_4789159).sum := by decide
  have hdescent : baseEnd_4789159 < baseStart_4789159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789255 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4789255 : Nat := 118140960795 + 4789255 * 2 ^ 59
def prefixEnd_4789255 : Nat := 4983230072969 + 3 ^ 40 * 4789255 * 2
def baseEnd_4789255 : Nat := 2459189791948764751487123

theorem tailTrace_4789255 : CollatzResearch.WordTrace tailWord_4789255 prefixEnd_4789255 2459189791948764751487123 := by
  unfold tailWord_4789255
  simp only [CollatzResearch.WordTrace]
  refine ⟨174678480264354549479609219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116452320176236366319739479 174678480264354549479609219)
  ·
    refine ⟨262017720396531824219413829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174678480264354549479609219 262017720396531824219413829)
    ·
      refine ⟨49128322574349717041140093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262017720396531824219413829 49128322574349717041140093)
      ·
        refine ⟨18423120965381143890427535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49128322574349717041140093 18423120965381143890427535)
        ·
          refine ⟨27634681448071715835641303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18423120965381143890427535 27634681448071715835641303)
          ·
            refine ⟨41452022172107573753461955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27634681448071715835641303 41452022172107573753461955)
            ·
              refine ⟨62178033258161360630192933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41452022172107573753461955 62178033258161360630192933)
              ·
                refine ⟨11658381235905255118161175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62178033258161360630192933 11658381235905255118161175)
                ·
                  refine ⟨17487571853857882677241763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11658381235905255118161175 17487571853857882677241763)
                  ·
                    refine ⟨26231357780786824015862645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17487571853857882677241763 26231357780786824015862645)
                    ·
                      refine ⟨2459189791948764751487123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26231357780786824015862645 2459189791948764751487123)
                      ·
                        rfl

theorem cell23_4789255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4789255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789255 prefixEnd_4789255 := by exact prefixLift 4789255
  have htrace : WordTrace (prefixWord ++ tailWord_4789255) baseStart_4789255 baseEnd_4789255 := by
    simpa [prefixWord, tailWord_4789255, baseEnd_4789255] using wordTrace_append hprefix tailTrace_4789255
  have hstable : (prefixWord ++ tailWord_4789255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789255).length < 2 ^ (prefixWord ++ tailWord_4789255).sum := by decide
  have hdescent : baseEnd_4789255 < baseStart_4789255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789266 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4789266 : Nat := 118140960795 + 4789266 * 2 ^ 59
def prefixEnd_4789266 : Nat := 4983230072969 + 3 ^ 40 * 4789266 * 2
def baseEnd_4789266 : Nat := 819731813411988069483191

theorem tailTrace_4789266 : CollatzResearch.WordTrace tailWord_4789266 prefixEnd_4789266 819731813411988069483191 := by
  unfold tailWord_4789266
  simp only [CollatzResearch.WordTrace]
  refine ⟨43669720366828674589564913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116452587644876465572173101 43669720366828674589564913)
  ·
    refine ⟨32752290275121505942173685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43669720366828674589564913 32752290275121505942173685)
    ·
      refine ⟨3070527213292641182078783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32752290275121505942173685 3070527213292641182078783)
      ·
        refine ⟨4605790819938961773118175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070527213292641182078783 4605790819938961773118175)
        ·
          refine ⟨6908686229908442659677263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4605790819938961773118175 6908686229908442659677263)
          ·
            refine ⟨10363029344862663989515895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6908686229908442659677263 10363029344862663989515895)
            ·
              refine ⟨15544544017293995984273843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10363029344862663989515895 15544544017293995984273843)
              ·
                refine ⟨23316816025940993976410765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15544544017293995984273843 23316816025940993976410765)
                ·
                  refine ⟨8743806009727872741154037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23316816025940993976410765 8743806009727872741154037)
                  ·
                    refine ⟨819731813411988069483191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8743806009727872741154037 819731813411988069483191)
                    ·
                      rfl

theorem cell23_4789266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4789266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789266 prefixEnd_4789266 := by exact prefixLift 4789266
  have htrace : WordTrace (prefixWord ++ tailWord_4789266) baseStart_4789266 baseEnd_4789266 := by
    simpa [prefixWord, tailWord_4789266, baseEnd_4789266] using wordTrace_append hprefix tailTrace_4789266
  have hstable : (prefixWord ++ tailWord_4789266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789266).length < 2 ^ (prefixWord ++ tailWord_4789266).sum := by decide
  have hdescent : baseEnd_4789266 < baseStart_4789266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789269 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_4789269 : Nat := 118140960795 + 4789269 * 2 ^ 59
def prefixEnd_4789269 : Nat := 4983230072969 + 3 ^ 40 * 4789269 * 2
def baseEnd_4789269 : Nat := 2459196980677927696712059

theorem tailTrace_4789269 : CollatzResearch.WordTrace tailWord_4789269 prefixEnd_4789269 2459196980677927696712059 := by
  unfold tailWord_4789269
  simp only [CollatzResearch.WordTrace]
  refine ⟨174678990886303829870618861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116452660590869219913745907 174678990886303829870618861)
  ·
    refine ⟨65504621582363936201482073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174678990886303829870618861 65504621582363936201482073)
    ·
      refine ⟨49128466186772952151111555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65504621582363936201482073 49128466186772952151111555)
      ·
        refine ⟨73692699280159428226667333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49128466186772952151111555 73692699280159428226667333)
        ·
          refine ⟨13817381115029892792500125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73692699280159428226667333 13817381115029892792500125)
          ·
            refine ⟨5181517918136209797187547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13817381115029892792500125 5181517918136209797187547)
            ·
              refine ⟨7772276877204314695781321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181517918136209797187547 7772276877204314695781321)
              ·
                refine ⟨5829207657903236021835991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7772276877204314695781321 5829207657903236021835991)
                ·
                  refine ⟨8743811486854854032753987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5829207657903236021835991 8743811486854854032753987)
                  ·
                    refine ⟨13115717230282281049130981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8743811486854854032753987 13115717230282281049130981)
                    ·
                      refine ⟨2459196980677927696712059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13115717230282281049130981 2459196980677927696712059)
                      ·
                        rfl

theorem cell23_4789269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_4789269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789269 prefixEnd_4789269 := by exact prefixLift 4789269
  have htrace : WordTrace (prefixWord ++ tailWord_4789269) baseStart_4789269 baseEnd_4789269 := by
    simpa [prefixWord, tailWord_4789269, baseEnd_4789269] using wordTrace_append hprefix tailTrace_4789269
  have hstable : (prefixWord ++ tailWord_4789269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789269).length < 2 ^ (prefixWord ++ tailWord_4789269).sum := by decide
  have hdescent : baseEnd_4789269 < baseStart_4789269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789272 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_4789272 : Nat := 118140960795 + 4789272 * 2 ^ 59
def prefixEnd_4789272 : Nat := 4983230072969 + 3 ^ 40 * 4789272 * 2
def baseEnd_4789272 : Nat := 2459198521119891184974545

theorem tailTrace_4789272 : CollatzResearch.WordTrace tailWord_4789272 prefixEnd_4789272 2459198521119891184974545 := by
  unfold tailWord_4789272
  simp only [CollatzResearch.WordTrace]
  refine ⟨87339550152646480691489035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116452733536861974255318713 87339550152646480691489035)
  ·
    refine ⟨131009325228969721037233553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87339550152646480691489035 131009325228969721037233553)
    ·
      refine ⟨98256993921727290777925165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131009325228969721037233553 98256993921727290777925165)
      ·
        refine ⟨36846372720647734041721937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98256993921727290777925165 36846372720647734041721937)
        ·
          refine ⟨27634779540485800531291453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36846372720647734041721937 27634779540485800531291453)
          ·
            refine ⟨10363042327682175199234295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27634779540485800531291453 10363042327682175199234295)
            ·
              refine ⟨15544563491523262798851443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10363042327682175199234295 15544563491523262798851443)
              ·
                refine ⟨23316845237284894198277165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15544563491523262798851443 23316845237284894198277165)
                ·
                  refine ⟨8743816963981835324353937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23316845237284894198277165 8743816963981835324353937)
                  ·
                    refine ⟨6557862722986376493265453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8743816963981835324353937 6557862722986376493265453)
                    ·
                      refine ⟨2459198521119891184974545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6557862722986376493265453 2459198521119891184974545)
                      ·
                        rfl

theorem cell23_4789272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_4789272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789272 prefixEnd_4789272 := by exact prefixLift 4789272
  have htrace : WordTrace (prefixWord ++ tailWord_4789272) baseStart_4789272 baseEnd_4789272 := by
    simpa [prefixWord, tailWord_4789272, baseEnd_4789272] using wordTrace_append hprefix tailTrace_4789272
  have hstable : (prefixWord ++ tailWord_4789272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789272).length < 2 ^ (prefixWord ++ tailWord_4789272).sum := by decide
  have hdescent : baseEnd_4789272 < baseStart_4789272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789282 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4789282 : Nat := 118140960795 + 4789282 * 2 ^ 59
def prefixEnd_4789282 : Nat := 4983230072969 + 3 ^ 40 * 4789282 * 2
def baseEnd_4789282 : Nat := 2459203655926436145849499

theorem tailTrace_4789282 : CollatzResearch.WordTrace tailWord_4789282 prefixEnd_4789282 2459203655926436145849499 := by
  unfold tailWord_4789282
  simp only [CollatzResearch.WordTrace]
  refine ⟨43669866258814183272710525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116452976690171155393894733 43669866258814183272710525)
  ·
    refine ⟨16376199847055318727266447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43669866258814183272710525 16376199847055318727266447)
    ·
      refine ⟨24564299770582978090899671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16376199847055318727266447 24564299770582978090899671)
      ·
        refine ⟨36846449655874467136349507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24564299770582978090899671 36846449655874467136349507)
        ·
          refine ⟨55269674483811700704524261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36846449655874467136349507 55269674483811700704524261)
          ·
            refine ⟨10363063965714693882098299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55269674483811700704524261 10363063965714693882098299)
            ·
              refine ⟨15544595948572040823147449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10363063965714693882098299 15544595948572040823147449)
              ·
                refine ⟨11658446961429030617360587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15544595948572040823147449 11658446961429030617360587)
                ·
                  refine ⟨17487670442143545926040881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11658446961429030617360587 17487670442143545926040881)
                  ·
                    refine ⟨13115752831607659444530661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17487670442143545926040881 13115752831607659444530661)
                    ·
                      refine ⟨2459203655926436145849499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13115752831607659444530661 2459203655926436145849499)
                      ·
                        rfl

theorem cell23_4789282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4789282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789282 prefixEnd_4789282 := by exact prefixLift 4789282
  have htrace : WordTrace (prefixWord ++ tailWord_4789282) baseStart_4789282 baseEnd_4789282 := by
    simpa [prefixWord, tailWord_4789282, baseEnd_4789282] using wordTrace_append hprefix tailTrace_4789282
  have hstable : (prefixWord ++ tailWord_4789282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789282).length < 2 ^ (prefixWord ++ tailWord_4789282).sum := by decide
  have hdescent : baseEnd_4789282 < baseStart_4789282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789305 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 2, 7]
def baseStart_4789305 : Nat := 118140960795 + 4789305 * 2 ^ 59
def prefixEnd_4789305 : Nat := 4983230072969 + 3 ^ 40 * 4789305 * 2
def baseEnd_4789305 : Nat := 819738488660496518620631

theorem tailTrace_4789305 : CollatzResearch.WordTrace tailWord_4789305 prefixEnd_4789305 819738488660496518620631 := by
  unfold tailWord_4789305
  simp only [CollatzResearch.WordTrace]
  refine ⟨174680303914173408018929369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116453535942782272012619579 174680303914173408018929369)
  ·
    refine ⟨131010227935630056014197027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174680303914173408018929369 131010227935630056014197027)
    ·
      refine ⟨196515341903445084021295541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131010227935630056014197027 196515341903445084021295541)
      ·
        refine ⟨18423313303447976626996457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196515341903445084021295541 18423313303447976626996457)
        ·
          refine ⟨13817484977585982470247343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18423313303447976626996457 13817484977585982470247343)
          ·
            refine ⟨20726227466378973705371015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13817484977585982470247343 20726227466378973705371015)
            ·
              refine ⟨31089341199568460558056523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20726227466378973705371015 31089341199568460558056523)
              ·
                refine ⟨46634011799352690837084785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31089341199568460558056523 46634011799352690837084785)
                ·
                  refine ⟨34975508849514518127813589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46634011799352690837084785 34975508849514518127813589)
                  ·
                    refine ⟨819738488660496518620631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34975508849514518127813589 819738488660496518620631)
                    ·
                      rfl

theorem cell23_4789305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_4789305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789305 prefixEnd_4789305 := by exact prefixLift 4789305
  have htrace : WordTrace (prefixWord ++ tailWord_4789305) baseStart_4789305 baseEnd_4789305 := by
    simpa [prefixWord, tailWord_4789305, baseEnd_4789305] using wordTrace_append hprefix tailTrace_4789305
  have hstable : (prefixWord ++ tailWord_4789305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789305).length < 2 ^ (prefixWord ++ tailWord_4789305).sum := by decide
  have hdescent : baseEnd_4789305 < baseStart_4789305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789312 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 5, 3, 2]
def baseStart_4789312 : Nat := 118140960795 + 4789312 * 2 ^ 59
def prefixEnd_4789312 : Nat := 4983230072969 + 3 ^ 40 * 4789312 * 2
def baseEnd_4789312 : Nat := 2459219060346071028474361

theorem tailTrace_4789312 : CollatzResearch.WordTrace tailWord_4789312 prefixEnd_4789312 2459219060346071028474361 := by
  unfold tailWord_4789312
  simp only [CollatzResearch.WordTrace]
  refine ⟨87340279612574024107217095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116453706150098698809622793 87340279612574024107217095)
  ·
    refine ⟨131010419418861036160825643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87340279612574024107217095 131010419418861036160825643)
    ·
      refine ⟨196515629128291554241238465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131010419418861036160825643 196515629128291554241238465)
      ·
        refine ⟨147386721846218665680928849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196515629128291554241238465 147386721846218665680928849)
        ·
          refine ⟨110540041384663999260696637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147386721846218665680928849 110540041384663999260696637)
          ·
            refine ⟨41452515519248999722761239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110540041384663999260696637 41452515519248999722761239)
            ·
              refine ⟨62178773278873499584141859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41452515519248999722761239 62178773278873499584141859)
              ·
                refine ⟨93268159918310249376212789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62178773278873499584141859 93268159918310249376212789)
                ·
                  refine ⟨8743889992341585879019949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93268159918310249376212789 8743889992341585879019949)
                  ·
                    refine ⟨3278958747128094704632481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8743889992341585879019949 3278958747128094704632481)
                    ·
                      refine ⟨2459219060346071028474361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278958747128094704632481 2459219060346071028474361)
                      ·
                        rfl

theorem cell23_4789312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_4789312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789312 prefixEnd_4789312 := by exact prefixLift 4789312
  have htrace : WordTrace (prefixWord ++ tailWord_4789312) baseStart_4789312 baseEnd_4789312 := by
    simpa [prefixWord, tailWord_4789312, baseEnd_4789312] using wordTrace_append hprefix tailTrace_4789312
  have hstable : (prefixWord ++ tailWord_4789312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789312).length < 2 ^ (prefixWord ++ tailWord_4789312).sum := by decide
  have hdescent : baseEnd_4789312 < baseStart_4789312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789319 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_4789319 : Nat := 118140960795 + 4789319 * 2 ^ 59
def prefixEnd_4789319 : Nat := 4983230072969 + 3 ^ 40 * 4789319 * 2
def baseEnd_4789319 : Nat := 2459222654710652501086829

theorem tailTrace_4789319 : CollatzResearch.WordTrace tailWord_4789319 prefixEnd_4789319 2459222654710652501086829 := by
  unfold tailWord_4789319
  simp only [CollatzResearch.WordTrace]
  refine ⟨174680814536122688409939011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116453876357415125606626007 174680814536122688409939011)
  ·
    refine ⟨262021221804184032614908517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174680814536122688409939011 262021221804184032614908517)
    ·
      refine ⟨49128979088284506115295347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262021221804184032614908517 49128979088284506115295347)
      ·
        refine ⟨73693468632426759172943021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49128979088284506115295347 73693468632426759172943021)
        ·
          refine ⟨27635050737160034689853633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73693468632426759172943021 27635050737160034689853633)
          ·
            refine ⟨20726288052870026017390225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27635050737160034689853633 20726288052870026017390225)
            ·
              refine ⟨15544716039652519513042669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20726288052870026017390225 15544716039652519513042669)
              ·
                refine ⟨5829268514869694817391001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15544716039652519513042669 5829268514869694817391001)
                ·
                  refine ⟨4371951386152271113043251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5829268514869694817391001 4371951386152271113043251)
                  ·
                    refine ⟨6557927079228406669564877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4371951386152271113043251 6557927079228406669564877)
                    ·
                      refine ⟨2459222654710652501086829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6557927079228406669564877 2459222654710652501086829)
                      ·
                        rfl

theorem cell23_4789319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_4789319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789319 prefixEnd_4789319 := by exact prefixLift 4789319
  have htrace : WordTrace (prefixWord ++ tailWord_4789319) baseStart_4789319 baseEnd_4789319 := by
    simpa [prefixWord, tailWord_4789319, baseEnd_4789319] using wordTrace_append hprefix tailTrace_4789319
  have hstable : (prefixWord ++ tailWord_4789319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789319).length < 2 ^ (prefixWord ++ tailWord_4789319).sum := by decide
  have hdescent : baseEnd_4789319 < baseStart_4789319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789345 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_4789345 : Nat := 118140960795 + 4789345 * 2 ^ 59
def prefixEnd_4789345 : Nat := 4983230072969 + 3 ^ 40 * 4789345 * 2
def baseEnd_4789345 : Nat := 2459236005207669399361709

theorem tailTrace_4789345 : CollatzResearch.WordTrace tailWord_4789345 prefixEnd_4789345 2459236005207669399361709 := by
  unfold tailWord_4789345
  simp only [CollatzResearch.WordTrace]
  refine ⟨174681762834028494850385489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116454508556018996566923659 174681762834028494850385489)
  ·
    refine ⟨131011322125521371137789117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174681762834028494850385489 131011322125521371137789117)
    ·
      refine ⟨49129245797070514176670919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131011322125521371137789117 49129245797070514176670919)
      ·
        refine ⟨73693868695605771265006379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49129245797070514176670919 73693868695605771265006379)
        ·
          refine ⟨110540803043408656897509569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73693868695605771265006379 110540803043408656897509569)
          ·
            refine ⟨82905602282556492673132177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110540803043408656897509569 82905602282556492673132177)
            ·
              refine ⟨62179201711917369504849133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82905602282556492673132177 62179201711917369504849133)
              ·
                refine ⟨23317200641969013564318425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62179201711917369504849133 23317200641969013564318425)
                ·
                  refine ⟨17487900481476760173238819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23317200641969013564318425 17487900481476760173238819)
                  ·
                    refine ⟨26231850722215140259858229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17487900481476760173238819 26231850722215140259858229)
                    ·
                      refine ⟨2459236005207669399361709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26231850722215140259858229 2459236005207669399361709)
                      ·
                        rfl

theorem cell23_4789345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_4789345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789345 prefixEnd_4789345 := by exact prefixLift 4789345
  have htrace : WordTrace (prefixWord ++ tailWord_4789345) baseStart_4789345 baseEnd_4789345 := by
    simpa [prefixWord, tailWord_4789345, baseEnd_4789345] using wordTrace_append hprefix tailTrace_4789345
  have hstable : (prefixWord ++ tailWord_4789345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789345).length < 2 ^ (prefixWord ++ tailWord_4789345).sum := by decide
  have hdescent : baseEnd_4789345 < baseStart_4789345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789359 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 4, 2, 2]
def baseStart_4789359 : Nat := 118140960795 + 4789359 * 2 ^ 59
def prefixEnd_4789359 : Nat := 4983230072969 + 3 ^ 40 * 4789359 * 2
def baseEnd_4789359 : Nat := 2459243193936832344586645

theorem tailTrace_4789359 : CollatzResearch.WordTrace tailWord_4789359 prefixEnd_4789359 2459243193936832344586645 := by
  unfold tailWord_4789359
  simp only [CollatzResearch.WordTrace]
  refine ⟨174682273455977775241395131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116454848970651850160930087 174682273455977775241395131)
  ·
    refine ⟨262023410183966662862092697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174682273455977775241395131 262023410183966662862092697)
    ·
      refine ⟨196517557637974997146569523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262023410183966662862092697 196517557637974997146569523)
      ·
        refine ⟨294776336456962495719854285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196517557637974997146569523 294776336456962495719854285)
        ·
          refine ⟨110541126171360935894945357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294776336456962495719854285 110541126171360935894945357)
          ·
            refine ⟨41452922314260350960604509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110541126171360935894945357 41452922314260350960604509)
            ·
              refine ⟨15544845867847631610226691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41452922314260350960604509 15544845867847631610226691)
              ·
                refine ⟨23317268801771447415340037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15544845867847631610226691 23317268801771447415340037)
                ·
                  refine ⟨4371987900332146390376257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23317268801771447415340037 4371987900332146390376257)
                  ·
                    refine ⟨3278990925249109792782193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4371987900332146390376257 3278990925249109792782193)
                    ·
                      refine ⟨2459243193936832344586645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3278990925249109792782193 2459243193936832344586645)
                      ·
                        rfl

theorem cell23_4789359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 2, 2].length) (baseStart_4789359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789359 prefixEnd_4789359 := by exact prefixLift 4789359
  have htrace : WordTrace (prefixWord ++ tailWord_4789359) baseStart_4789359 baseEnd_4789359 := by
    simpa [prefixWord, tailWord_4789359, baseEnd_4789359] using wordTrace_append hprefix tailTrace_4789359
  have hstable : (prefixWord ++ tailWord_4789359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789359).length < 2 ^ (prefixWord ++ tailWord_4789359).sum := by decide
  have hdescent : baseEnd_4789359 < baseStart_4789359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789395 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 1, 7]
def baseStart_4789395 : Nat := 118140960795 + 4789395 * 2 ^ 59
def prefixEnd_4789395 : Nat := 4983230072969 + 3 ^ 40 * 4789395 * 2
def baseEnd_4789395 : Nat := 819753893080131401245493

theorem tailTrace_4789395 : CollatzResearch.WordTrace tailWord_4789395 prefixEnd_4789395 819753893080131401245493 := by
  unfold tailWord_4789395
  simp only [CollatzResearch.WordTrace]
  refine ⟨174683586483847353389705639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116455724322564902259803759 174683586483847353389705639)
  ·
    refine ⟨262025379725771030084558459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174683586483847353389705639 262025379725771030084558459)
    ·
      refine ⟨393038069588656545126837689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262025379725771030084558459 393038069588656545126837689)
      ·
        refine ⟨294778552191492408845128267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393038069588656545126837689 294778552191492408845128267)
        ·
          refine ⟨442167828287238613267692401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294778552191492408845128267 442167828287238613267692401)
          ·
            refine ⟨331625871215428959950769301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442167828287238613267692401 331625871215428959950769301)
            ·
              refine ⟨15544962713223232497692311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 331625871215428959950769301 15544962713223232497692311)
              ·
                refine ⟨23317444069834848746538467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15544962713223232497692311 23317444069834848746538467)
                ·
                  refine ⟨34976166104752273119807701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23317444069834848746538467 34976166104752273119807701)
                  ·
                    refine ⟨819753893080131401245493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34976166104752273119807701 819753893080131401245493)
                    ·
                      rfl

theorem cell23_4789395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 7].length) (baseStart_4789395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789395 prefixEnd_4789395 := by exact prefixLift 4789395
  have htrace : WordTrace (prefixWord ++ tailWord_4789395) baseStart_4789395 baseEnd_4789395 := by
    simpa [prefixWord, tailWord_4789395, baseEnd_4789395] using wordTrace_append hprefix tailTrace_4789395
  have hstable : (prefixWord ++ tailWord_4789395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789395).length < 2 ^ (prefixWord ++ tailWord_4789395).sum := by decide
  have hdescent : baseEnd_4789395 < baseStart_4789395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789399 : List Nat := [1, 1, 3, 3, 3, 1, 3, 3, 5]
def baseStart_4789399 : Nat := 118140960795 + 4789399 * 2 ^ 59
def prefixEnd_4789399 : Nat := 4983230072969 + 3 ^ 40 * 4789399 * 2
def baseEnd_4789399 : Nat := 273251525907001354231829

theorem tailTrace_4789399 : CollatzResearch.WordTrace tailWord_4789399 prefixEnd_4789399 273251525907001354231829 := by
  unfold tailWord_4789399
  simp only [CollatzResearch.WordTrace]
  refine ⟨174683732375832862072851251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116455821583888574715234167 174683732375832862072851251)
  ·
    refine ⟨262025598563749293109276877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174683732375832862072851251 262025598563749293109276877)
    ·
      refine ⟨98259599461405984915978829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262025598563749293109276877 98259599461405984915978829)
      ·
        refine ⟨36847349798027244343492061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98259599461405984915978829 36847349798027244343492061)
        ·
          refine ⟨13817756174260216628809523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36847349798027244343492061 13817756174260216628809523)
          ·
            refine ⟨20726634261390324943214285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13817756174260216628809523 20726634261390324943214285)
            ·
              refine ⟨7772487848021371853705357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20726634261390324943214285 7772487848021371853705357)
              ·
                refine ⟨2914682943008014445139509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7772487848021371853705357 2914682943008014445139509)
                ·
                  refine ⟨273251525907001354231829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2914682943008014445139509 273251525907001354231829)
                  ·
                    rfl

theorem cell23_4789399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 5].length) (baseStart_4789399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789399 prefixEnd_4789399 := by exact prefixLift 4789399
  have htrace : WordTrace (prefixWord ++ tailWord_4789399) baseStart_4789399 baseEnd_4789399 := by
    simpa [prefixWord, tailWord_4789399, baseEnd_4789399] using wordTrace_append hprefix tailTrace_4789399
  have hstable : (prefixWord ++ tailWord_4789399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789399).length < 2 ^ (prefixWord ++ tailWord_4789399).sum := by decide
  have hdescent : baseEnd_4789399 < baseStart_4789399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789412 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_4789412 : Nat := 118140960795 + 4789412 * 2 ^ 59
def prefixEnd_4789412 : Nat := 4983230072969 + 3 ^ 40 * 4789412 * 2
def baseEnd_4789412 : Nat := 819756802803840212407967

theorem tailTrace_4789412 : CollatzResearch.WordTrace tailWord_4789412 prefixEnd_4789412 819756802803840212407967 := by
  unfold tailWord_4789412
  simp only [CollatzResearch.WordTrace]
  refine ⟨87342103262392882646537245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116456137683190510195382993 87342103262392882646537245)
  ·
    refine ⟨32753288723397330992451467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87342103262392882646537245 32753288723397330992451467)
    ·
      refine ⟨49129933085095996488677201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32753288723397330992451467 49129933085095996488677201)
      ·
        refine ⟨36847449813821997366507901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49129933085095996488677201 36847449813821997366507901)
        ·
          refine ⟨13817793680183249012440463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36847449813821997366507901 13817793680183249012440463)
          ·
            refine ⟨20726690520274873518660695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13817793680183249012440463 20726690520274873518660695)
            ·
              refine ⟨31090035780412310277991043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20726690520274873518660695 31090035780412310277991043)
              ·
                refine ⟨46635053670618465416986565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31090035780412310277991043 46635053670618465416986565)
                ·
                  refine ⟨8744072563240962265684981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46635053670618465416986565 8744072563240962265684981)
                  ·
                    refine ⟨819756802803840212407967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8744072563240962265684981 819756802803840212407967)
                    ·
                      rfl

theorem cell23_4789412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_4789412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789412 prefixEnd_4789412 := by exact prefixLift 4789412
  have htrace : WordTrace (prefixWord ++ tailWord_4789412) baseStart_4789412 baseEnd_4789412 := by
    simpa [prefixWord, tailWord_4789412, baseEnd_4789412] using wordTrace_append hprefix tailTrace_4789412
  have hstable : (prefixWord ++ tailWord_4789412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789412).length < 2 ^ (prefixWord ++ tailWord_4789412).sum := by decide
  have hdescent : baseEnd_4789412 < baseStart_4789412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789445 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_4789445 : Nat := 118140960795 + 4789445 * 2 ^ 59
def prefixEnd_4789445 : Nat := 4983230072969 + 3 ^ 40 * 4789445 * 2
def baseEnd_4789445 : Nat := 2459287353273119008111249

theorem tailTrace_4789445 : CollatzResearch.WordTrace tailWord_4789445 prefixEnd_4789445 2459287353273119008111249 := by
  unfold tailWord_4789445
  simp only [CollatzResearch.WordTrace]
  refine ⟨174685410133666211929025789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116456940089110807952683859 174685410133666211929025789)
  ·
    refine ⟨65507028800124829473384671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174685410133666211929025789 65507028800124829473384671)
    ·
      refine ⟨98260543200187244210077007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65507028800124829473384671 98260543200187244210077007)
      ·
        refine ⟨147390814800280866315115511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98260543200187244210077007 147390814800280866315115511)
        ·
          refine ⟨221086222200421299472673267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147390814800280866315115511 221086222200421299472673267)
          ·
            refine ⟨331629333300631949209009901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221086222200421299472673267 331629333300631949209009901)
            ·
              refine ⟨124360999987736980953378713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 331629333300631949209009901 124360999987736980953378713)
              ·
                refine ⟨93270749990802735715034035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124360999987736980953378713 93270749990802735715034035)
                ·
                  refine ⟨139906124986204103572551053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93270749990802735715034035 139906124986204103572551053)
                  ·
                    refine ⟨52464796869826538839706645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139906124986204103572551053 52464796869826538839706645)
                    ·
                      refine ⟨2459287353273119008111249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52464796869826538839706645 2459287353273119008111249)
                      ·
                        rfl

theorem cell23_4789445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_4789445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789445 prefixEnd_4789445 := by exact prefixLift 4789445
  have htrace : WordTrace (prefixWord ++ tailWord_4789445) baseStart_4789445 baseEnd_4789445 := by
    simpa [prefixWord, tailWord_4789445, baseEnd_4789445] using wordTrace_append hprefix tailTrace_4789445
  have hstable : (prefixWord ++ tailWord_4789445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789445).length < 2 ^ (prefixWord ++ tailWord_4789445).sum := by decide
  have hdescent : baseEnd_4789445 < baseStart_4789445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789455 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 8]
def baseStart_4789455 : Nat := 118140960795 + 4789455 * 2 ^ 59
def prefixEnd_4789455 : Nat := 4983230072969 + 3 ^ 40 * 4789455 * 2
def baseEnd_4789455 : Nat := 273254720897740440998467

theorem tailTrace_4789455 : CollatzResearch.WordTrace tailWord_4789455 prefixEnd_4789455 273254720897740440998467 := by
  unfold tailWord_4789455
  simp only [CollatzResearch.WordTrace]
  refine ⟨174685774863629983636889819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116457183242419989091259879 174685774863629983636889819)
  ·
    refine ⟨262028662295444975455334729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174685774863629983636889819 262028662295444975455334729)
    ·
      refine ⟨196521496721583731591501047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262028662295444975455334729 196521496721583731591501047)
      ·
        refine ⟨294782245082375597387251571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196521496721583731591501047 294782245082375597387251571)
        ·
          refine ⟨442173367623563396080877357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294782245082375597387251571 442173367623563396080877357)
          ·
            refine ⟨165815012858836273530329009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 442173367623563396080877357 165815012858836273530329009)
            ·
              refine ⟨124361259644127205147746757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165815012858836273530329009 124361259644127205147746757)
              ·
                refine ⟨23317736183273850965202517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124361259644127205147746757 23317736183273850965202517)
                ·
                  refine ⟨273254720897740440998467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23317736183273850965202517 273254720897740440998467)
                  ·
                    rfl

theorem cell23_4789455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 8].length) (baseStart_4789455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789455 prefixEnd_4789455 := by exact prefixLift 4789455
  have htrace : WordTrace (prefixWord ++ tailWord_4789455) baseStart_4789455 baseEnd_4789455 := by
    simpa [prefixWord, tailWord_4789455, baseEnd_4789455] using wordTrace_append hprefix tailTrace_4789455
  have hstable : (prefixWord ++ tailWord_4789455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789455).length < 2 ^ (prefixWord ++ tailWord_4789455).sum := by decide
  have hdescent : baseEnd_4789455 < baseStart_4789455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789472 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 6]
def baseStart_4789472 : Nat := 118140960795 + 4789472 * 2 ^ 59
def prefixEnd_4789472 : Nat := 4983230072969 + 3 ^ 40 * 4789472 * 2
def baseEnd_4789472 : Nat := 273255690805643378052625

theorem tailTrace_4789472 : CollatzResearch.WordTrace tailWord_4789472 prefixEnd_4789472 273255690805643378052625 := by
  unfold tailWord_4789472
  simp only [CollatzResearch.WordTrace]
  refine ⟨87343197452284197770129335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116457596603045597026839113 87343197452284197770129335)
  ·
    refine ⟨131014796178426296655194003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87343197452284197770129335 131014796178426296655194003)
    ·
      refine ⟨196522194267639444982791005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131014796178426296655194003 196522194267639444982791005)
      ·
        refine ⟨73695822850364791868546627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196522194267639444982791005 73695822850364791868546627)
        ·
          refine ⟨110543734275547187802819941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73695822850364791868546627 110543734275547187802819941)
          ·
            refine ⟨20726950176665097713028739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110543734275547187802819941 20726950176665097713028739)
            ·
              refine ⟨31090425264997646569543109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20726950176665097713028739 31090425264997646569543109)
              ·
                refine ⟨5829454737187058731789333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31090425264997646569543109 5829454737187058731789333)
                ·
                  refine ⟨273255690805643378052625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5829454737187058731789333 273255690805643378052625)
                  ·
                    rfl

theorem cell23_4789472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 6].length) (baseStart_4789472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789472 prefixEnd_4789472 := by exact prefixLift 4789472
  have htrace : WordTrace (prefixWord ++ tailWord_4789472) baseStart_4789472 baseEnd_4789472 := by
    simpa [prefixWord, tailWord_4789472, baseEnd_4789472] using wordTrace_append hprefix tailTrace_4789472
  have hstable : (prefixWord ++ tailWord_4789472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789472).length < 2 ^ (prefixWord ++ tailWord_4789472).sum := by decide
  have hdescent : baseEnd_4789472 < baseStart_4789472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789509 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 1, 5, 2]
def baseStart_4789509 : Nat := 118140960795 + 4789509 * 2 ^ 59
def prefixEnd_4789509 : Nat := 4983230072969 + 3 ^ 40 * 4789509 * 2
def baseEnd_4789509 : Nat := 2459320216035006757710955

theorem tailTrace_4789509 : CollatzResearch.WordTrace tailWord_4789509 prefixEnd_4789509 2459320216035006757710955 := by
  unfold tailWord_4789509
  simp only [CollatzResearch.WordTrace]
  refine ⟨174687744405434350859355581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116458496270289567239570387 174687744405434350859355581)
  ·
    refine ⟨65507904152037881572258343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174687744405434350859355581 65507904152037881572258343)
    ·
      refine ⟨98261856228056822358387515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65507904152037881572258343 98261856228056822358387515)
      ·
        refine ⟨147392784342085233537581273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98261856228056822358387515 147392784342085233537581273)
        ·
          refine ⟨110544588256563925153185955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147392784342085233537581273 110544588256563925153185955)
          ·
            refine ⟨165816882384845887729778933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110544588256563925153185955 165816882384845887729778933)
            ·
              refine ⟨15545332723579301974666775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165816882384845887729778933 15545332723579301974666775)
              ·
                refine ⟨23317999085368952962000163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15545332723579301974666775 23317999085368952962000163)
                ·
                  refine ⟨34976998628053429443000245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23317999085368952962000163 34976998628053429443000245)
                  ·
                    refine ⟨3279093621380009010281273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34976998628053429443000245 3279093621380009010281273)
                    ·
                      refine ⟨2459320216035006757710955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279093621380009010281273 2459320216035006757710955)
                      ·
                        rfl

theorem cell23_4789509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_4789509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789509 prefixEnd_4789509 := by exact prefixLift 4789509
  have htrace : WordTrace (prefixWord ++ tailWord_4789509) baseStart_4789509 baseEnd_4789509 := by
    simpa [prefixWord, tailWord_4789509, baseEnd_4789509] using wordTrace_append hprefix tailTrace_4789509
  have hstable : (prefixWord ++ tailWord_4789509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789509).length < 2 ^ (prefixWord ++ tailWord_4789509).sum := by decide
  have hdescent : baseEnd_4789509 < baseStart_4789509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789532 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_4789532 : Nat := 118140960795 + 4789532 * 2 ^ 59
def prefixEnd_4789532 : Nat := 4983230072969 + 3 ^ 40 * 4789532 * 2
def baseEnd_4789532 : Nat := 819777342030020055907783

theorem tailTrace_4789532 : CollatzResearch.WordTrace tailWord_4789532 prefixEnd_4789532 819777342030020055907783 := by
  unfold tailWord_4789532
  simp only [CollatzResearch.WordTrace]
  refine ⟨87344291642175512893721425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116459055522900683858295233 87344291642175512893721425)
  ·
    refine ⟨65508218731631634670291069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87344291642175512893721425 65508218731631634670291069)
    ·
      refine ⟨24565582024361863001359151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65508218731631634670291069 24565582024361863001359151)
      ·
        refine ⟨36848373036542794502038727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24565582024361863001359151 36848373036542794502038727)
        ·
          refine ⟨55272559554814191753058091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36848373036542794502038727 55272559554814191753058091)
          ·
            refine ⟨82908839332221287629587137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55272559554814191753058091 82908839332221287629587137)
            ·
              refine ⟨62181629499165965722190353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82908839332221287629587137 62181629499165965722190353)
              ·
                refine ⟨46636222124374474291642765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62181629499165965722190353 46636222124374474291642765)
                ·
                  refine ⟨17488583296640427859366037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46636222124374474291642765 17488583296640427859366037)
                  ·
                    refine ⟨819777342030020055907783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17488583296640427859366037 819777342030020055907783)
                    ·
                      rfl

theorem cell23_4789532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_4789532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789532 prefixEnd_4789532 := by exact prefixLift 4789532
  have htrace : WordTrace (prefixWord ++ tailWord_4789532) baseStart_4789532 baseEnd_4789532 := by
    simpa [prefixWord, tailWord_4789532, baseEnd_4789532] using wordTrace_append hprefix tailTrace_4789532
  have hstable : (prefixWord ++ tailWord_4789532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789532).length < 2 ^ (prefixWord ++ tailWord_4789532).sum := by decide
  have hdescent : baseEnd_4789532 < baseStart_4789532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789533 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_4789533 : Nat := 118140960795 + 4789533 * 2 ^ 59
def prefixEnd_4789533 : Nat := 4983230072969 + 3 ^ 40 * 4789533 * 2
def baseEnd_4789533 : Nat := 2459332539570714663810845

theorem tailTrace_4789533 : CollatzResearch.WordTrace tailWord_4789533 prefixEnd_4789533 2459332539570714663810845 := by
  unfold tailWord_4789533
  simp only [CollatzResearch.WordTrace]
  refine ⟨174688619757347402958229253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116459079838231601972152835 174688619757347402958229253)
  ·
    refine ⟨32754116204502638054667985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174688619757347402958229253 32754116204502638054667985)
    ·
      refine ⟨24565587153376978541000989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32754116204502638054667985 24565587153376978541000989)
      ·
        refine ⟨9212095182516366952875371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24565587153376978541000989 9212095182516366952875371)
        ·
          refine ⟨13818142773774550429313057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9212095182516366952875371 13818142773774550429313057)
          ·
            refine ⟨10363607080330912821984793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13818142773774550429313057 10363607080330912821984793)
            ·
              refine ⟨7772705310248184616488595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10363607080330912821984793 7772705310248184616488595)
              ·
                refine ⟨11659057965372276924732893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7772705310248184616488595 11659057965372276924732893)
                ·
                  refine ⟨4372146737014603846774835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11659057965372276924732893 4372146737014603846774835)
                  ·
                    refine ⟨6558220105521905770162253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4372146737014603846774835 6558220105521905770162253)
                    ·
                      refine ⟨2459332539570714663810845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6558220105521905770162253 2459332539570714663810845)
                      ·
                        rfl

theorem cell23_4789533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_4789533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789533 prefixEnd_4789533 := by exact prefixLift 4789533
  have htrace : WordTrace (prefixWord ++ tailWord_4789533) baseStart_4789533 baseEnd_4789533 := by
    simpa [prefixWord, tailWord_4789533, baseEnd_4789533] using wordTrace_append hprefix tailTrace_4789533
  have hstable : (prefixWord ++ tailWord_4789533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789533).length < 2 ^ (prefixWord ++ tailWord_4789533).sum := by decide
  have hdescent : baseEnd_4789533 < baseStart_4789533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789552 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_4789552 : Nat := 118140960795 + 4789552 * 2 ^ 59
def prefixEnd_4789552 : Nat := 4983230072969 + 3 ^ 40 * 4789552 * 2
def baseEnd_4789552 : Nat := 2459342295703150089473257

theorem tailTrace_4789552 : CollatzResearch.WordTrace tailWord_4789552 prefixEnd_4789552 2459342295703150089473257 := by
  unfold tailWord_4789552
  simp only [CollatzResearch.WordTrace]
  refine ⟨87344656372139284601585455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116459541829519046135447273 87344656372139284601585455)
  ·
    refine ⟨131016984558208926902378183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87344656372139284601585455 131016984558208926902378183)
    ·
      refine ⟨196525476837313390353567275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131016984558208926902378183 196525476837313390353567275)
      ·
        refine ⟨294788215255970085530350913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196525476837313390353567275 294788215255970085530350913)
        ·
          refine ⟨221091161441977564147763185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294788215255970085530350913 221091161441977564147763185)
          ·
            refine ⟨165818371081483173110822389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221091161441977564147763185 165818371081483173110822389)
            ·
              refine ⟨15545472288889047479139599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165818371081483173110822389 15545472288889047479139599)
              ·
                refine ⟨23318208433333571218709399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15545472288889047479139599 23318208433333571218709399)
                ·
                  refine ⟨34977312650000356828064099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23318208433333571218709399 34977312650000356828064099)
                  ·
                    refine ⟨52465968975000535242096149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34977312650000356828064099 52465968975000535242096149)
                    ·
                      refine ⟨2459342295703150089473257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52465968975000535242096149 2459342295703150089473257)
                      ·
                        rfl

theorem cell23_4789552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_4789552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789552 prefixEnd_4789552 := by exact prefixLift 4789552
  have htrace : WordTrace (prefixWord ++ tailWord_4789552) baseStart_4789552 baseEnd_4789552 := by
    simpa [prefixWord, tailWord_4789552, baseEnd_4789552] using wordTrace_append hprefix tailTrace_4789552
  have hstable : (prefixWord ++ tailWord_4789552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789552).length < 2 ^ (prefixWord ++ tailWord_4789552).sum := by decide
  have hdescent : baseEnd_4789552 < baseStart_4789552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789556 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_4789556 : Nat := 118140960795 + 4789556 * 2 ^ 59
def prefixEnd_4789556 : Nat := 4983230072969 + 3 ^ 40 * 4789556 * 2
def baseEnd_4789556 : Nat := 2459344349625768073823239

theorem tailTrace_4789556 : CollatzResearch.WordTrace tailWord_4789556 prefixEnd_4789556 2459344349625768073823239 := by
  unfold tailWord_4789556
  simp only [CollatzResearch.WordTrace]
  refine ⟨87344729318132038943158261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116459639090842718590877681 87344729318132038943158261)
  ·
    refine ⟨8188568373574878650921087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87344729318132038943158261 8188568373574878650921087)
    ·
      refine ⟨12282852560362317976381631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8188568373574878650921087 12282852560362317976381631)
      ·
        refine ⟨18424278840543476964572447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12282852560362317976381631 18424278840543476964572447)
        ·
          refine ⟨27636418260815215446858671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18424278840543476964572447 27636418260815215446858671)
          ·
            refine ⟨41454627391222823170288007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27636418260815215446858671 41454627391222823170288007)
            ·
              refine ⟨62181941086834234755432011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41454627391222823170288007 62181941086834234755432011)
              ·
                refine ⟨93272911630251352133148017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62181941086834234755432011 93272911630251352133148017)
                ·
                  refine ⟨69954683722688514099861013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93272911630251352133148017 69954683722688514099861013)
                  ·
                    refine ⟨3279125799501024098430985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69954683722688514099861013 3279125799501024098430985)
                    ·
                      refine ⟨2459344349625768073823239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279125799501024098430985 2459344349625768073823239)
                      ·
                        rfl

theorem cell23_4789556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_4789556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789556 prefixEnd_4789556 := by exact prefixLift 4789556
  have htrace : WordTrace (prefixWord ++ tailWord_4789556) baseStart_4789556 baseEnd_4789556 := by
    simpa [prefixWord, tailWord_4789556, baseEnd_4789556] using wordTrace_append hprefix tailTrace_4789556
  have hstable : (prefixWord ++ tailWord_4789556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789556).length < 2 ^ (prefixWord ++ tailWord_4789556).sum := by decide
  have hdescent : baseEnd_4789556 < baseStart_4789556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789562 : List Nat := [3, 1, 1, 1, 4, 1, 3, 9]
def baseStart_4789562 : Nat := 118140960795 + 4789562 * 2 ^ 59
def prefixEnd_4789562 : Nat := 4983230072969 + 3 ^ 40 * 4789562 * 2
def baseEnd_4789562 : Nat := 91086941870729446309193

theorem tailTrace_4789562 : CollatzResearch.WordTrace tailWord_4789562 prefixEnd_4789562 91086941870729446309193 := by
  unfold tailWord_4789562
  simp only [CollatzResearch.WordTrace]
  refine ⟨43672419368560585227758735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116459784982828227274023293 43672419368560585227758735)
  ·
    refine ⟨65508629052840877841638103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43672419368560585227758735 65508629052840877841638103)
    ·
      refine ⟨98262943579261316762457155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65508629052840877841638103 98262943579261316762457155)
      ·
        refine ⟨147394415368891975143685733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98262943579261316762457155 147394415368891975143685733)
        ·
          refine ⟨27636452881667245339441075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147394415368891975143685733 27636452881667245339441075)
          ·
            refine ⟨41454679322500868009161613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27636452881667245339441075 41454679322500868009161613)
            ·
              refine ⟨15545504745937825503435605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41454679322500868009161613 15545504745937825503435605)
              ·
                refine ⟨91086941870729446309193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15545504745937825503435605 91086941870729446309193)
                ·
                  rfl

theorem cell23_4789562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_4789562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789562 prefixEnd_4789562 := by exact prefixLift 4789562
  have htrace : WordTrace (prefixWord ++ tailWord_4789562) baseStart_4789562 baseEnd_4789562 := by
    simpa [prefixWord, tailWord_4789562, baseEnd_4789562] using wordTrace_append hprefix tailTrace_4789562
  have hstable : (prefixWord ++ tailWord_4789562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789562).length < 2 ^ (prefixWord ++ tailWord_4789562).sum := by decide
  have hdescent : baseEnd_4789562 < baseStart_4789562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789592 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 2, 7]
def baseStart_4789592 : Nat := 118140960795 + 4789592 * 2 ^ 59
def prefixEnd_4789592 : Nat := 4983230072969 + 3 ^ 40 * 4789592 * 2
def baseEnd_4789592 : Nat := 819787611643109977657691

theorem tailTrace_4789592 : CollatzResearch.WordTrace tailWord_4789592 prefixEnd_4789592 819787611643109977657691 := by
  unfold tailWord_4789592
  simp only [CollatzResearch.WordTrace]
  refine ⟨87345385832066828017313515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116460514442755770689751353 87345385832066828017313515)
  ·
    refine ⟨131018078748100242025970273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87345385832066828017313515 131018078748100242025970273)
    ·
      refine ⟨98263559061075181519477705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131018078748100242025970273 98263559061075181519477705)
      ·
        refine ⟨73697669295806386139608279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98263559061075181519477705 73697669295806386139608279)
        ·
          refine ⟨110546503943709579209412419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73697669295806386139608279 110546503943709579209412419)
          ·
            refine ⟨165819755915564368814118629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110546503943709579209412419 165819755915564368814118629)
            ·
              refine ⟨31091204234168319152647243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165819755915564368814118629 31091204234168319152647243)
              ·
                refine ⟨46636806351252478728970865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31091204234168319152647243 46636806351252478728970865)
                ·
                  refine ⟨34977604763439359046728149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46636806351252478728970865 34977604763439359046728149)
                  ·
                    refine ⟨819787611643109977657691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34977604763439359046728149 819787611643109977657691)
                    ·
                      rfl

theorem cell23_4789592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_4789592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789592 prefixEnd_4789592 := by exact prefixLift 4789592
  have htrace : WordTrace (prefixWord ++ tailWord_4789592) baseStart_4789592 baseEnd_4789592 := by
    simpa [prefixWord, tailWord_4789592, baseEnd_4789592] using wordTrace_append hprefix tailTrace_4789592
  have hstable : (prefixWord ++ tailWord_4789592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789592).length < 2 ^ (prefixWord ++ tailWord_4789592).sum := by decide
  have hdescent : baseEnd_4789592 < baseStart_4789592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789599 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 7, 2]
def baseStart_4789599 : Nat := 118140960795 + 4789599 * 2 ^ 59
def prefixEnd_4789599 : Nat := 4983230072969 + 3 ^ 40 * 4789599 * 2
def baseEnd_4789599 : Nat := 2459366429293911405585541

theorem tailTrace_4789599 : CollatzResearch.WordTrace tailWord_4789599 prefixEnd_4789599 2459366429293911405585541 := by
  unfold tailWord_4789599
  simp only [CollatzResearch.WordTrace]
  refine ⟨174691026975108296230131851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116460684650072197486754567 174691026975108296230131851)
  ·
    refine ⟨262036540462662444345197777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174691026975108296230131851 262036540462662444345197777)
    ·
      refine ⟨196527405346996833258898333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262036540462662444345197777 196527405346996833258898333)
      ·
        refine ⟨73697777005123812472086875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196527405346996833258898333 73697777005123812472086875)
        ·
          refine ⟨110546665507685718708130313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73697777005123812472086875 110546665507685718708130313)
          ·
            refine ⟨82909999130764289031097735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110546665507685718708130313 82909999130764289031097735)
            ·
              refine ⟨124364998696146433546646603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82909999130764289031097735 124364998696146433546646603)
              ·
                refine ⟨186547498044219650319969905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124364998696146433546646603 186547498044219650319969905)
                ·
                  refine ⟨139910623533164737739977429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186547498044219650319969905 139910623533164737739977429)
                  ·
                    refine ⟨3279155239058548540780721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 139910623533164737739977429 3279155239058548540780721)
                    ·
                      refine ⟨2459366429293911405585541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279155239058548540780721 2459366429293911405585541)
                      ·
                        rfl

theorem cell23_4789599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_4789599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789599 prefixEnd_4789599 := by exact prefixLift 4789599
  have htrace : WordTrace (prefixWord ++ tailWord_4789599) baseStart_4789599 baseEnd_4789599 := by
    simpa [prefixWord, tailWord_4789599, baseEnd_4789599] using wordTrace_append hprefix tailTrace_4789599
  have hstable : (prefixWord ++ tailWord_4789599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789599).length < 2 ^ (prefixWord ++ tailWord_4789599).sum := by decide
  have hdescent : baseEnd_4789599 < baseStart_4789599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789610 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4789610 : Nat := 118140960795 + 4789610 * 2 ^ 59
def prefixEnd_4789610 : Nat := 4983230072969 + 3 ^ 40 * 4789610 * 2
def baseEnd_4789610 : Nat := 2459372077581110862547991

theorem tailTrace_4789610 : CollatzResearch.WordTrace tailWord_4789610 prefixEnd_4789610 2459372077581110862547991 := by
  unfold tailWord_4789610
  simp only [CollatzResearch.WordTrace]
  refine ⟨43672857044517111277195571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116460952118712296739188189 43672857044517111277195571)
  ·
    refine ⟨65509285566775666915793357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43672857044517111277195571 65509285566775666915793357)
    ·
      refine ⟨24565982087540875093422509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65509285566775666915793357 24565982087540875093422509)
      ·
        refine ⟨9212243282827828160033441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24565982087540875093422509 9212243282827828160033441)
        ·
          refine ⟨6909182462120871120025081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9212243282827828160033441 6909182462120871120025081)
          ·
            refine ⟨5181886846590653340018811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6909182462120871120025081 5181886846590653340018811)
            ·
              refine ⟨7772830269885980010028217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181886846590653340018811 7772830269885980010028217)
              ·
                refine ⟨5829622702414485007521163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7772830269885980010028217 5829622702414485007521163)
                ·
                  refine ⟨8744434053621727511281745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5829622702414485007521163 8744434053621727511281745)
                  ·
                    refine ⟨6558325540216295633461309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8744434053621727511281745 6558325540216295633461309)
                    ·
                      refine ⟨2459372077581110862547991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6558325540216295633461309 2459372077581110862547991)
                      ·
                        rfl

theorem cell23_4789610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4789610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789610 prefixEnd_4789610 := by exact prefixLift 4789610
  have htrace : WordTrace (prefixWord ++ tailWord_4789610) baseStart_4789610 baseEnd_4789610 := by
    simpa [prefixWord, tailWord_4789610, baseEnd_4789610] using wordTrace_append hprefix tailTrace_4789610
  have hstable : (prefixWord ++ tailWord_4789610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789610).length < 2 ^ (prefixWord ++ tailWord_4789610).sum := by decide
  have hdescent : baseEnd_4789610 < baseStart_4789610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789616 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 3, 3, 2]
def baseStart_4789616 : Nat := 118140960795 + 4789616 * 2 ^ 59
def prefixEnd_4789616 : Nat := 4983230072969 + 3 ^ 40 * 4789616 * 2
def baseEnd_4789616 : Nat := 2459375158465037839072963

theorem tailTrace_4789616 : CollatzResearch.WordTrace tailWord_4789616 prefixEnd_4789616 2459375158465037839072963 := by
  unfold tailWord_4789616
  simp only [CollatzResearch.WordTrace]
  refine ⟨87345823508023354066750351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116461098010697805422333801 87345823508023354066750351)
  ·
    refine ⟨131018735262035031100125527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87345823508023354066750351 131018735262035031100125527)
    ·
      refine ⟨196528102893052546650188291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131018735262035031100125527 196528102893052546650188291)
      ·
        refine ⟨294792154339578819975282437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196528102893052546650188291 294792154339578819975282437)
        ·
          refine ⟨55273528938671028745365457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294792154339578819975282437 55273528938671028745365457)
          ·
            refine ⟨41455146704003271559024093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55273528938671028745365457 41455146704003271559024093)
            ·
              refine ⟨15545680014001226834634035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41455146704003271559024093 15545680014001226834634035)
              ·
                refine ⟨23318520021001840251951053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15545680014001226834634035 23318520021001840251951053)
                ·
                  refine ⟨8744445007875690094481645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23318520021001840251951053 8744445007875690094481645)
                  ·
                    refine ⟨3279166877953383785430617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8744445007875690094481645 3279166877953383785430617)
                    ·
                      refine ⟨2459375158465037839072963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279166877953383785430617 2459375158465037839072963)
                      ·
                        rfl

theorem cell23_4789616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 3, 2].length) (baseStart_4789616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789616 prefixEnd_4789616 := by exact prefixLift 4789616
  have htrace : WordTrace (prefixWord ++ tailWord_4789616) baseStart_4789616 baseEnd_4789616 := by
    simpa [prefixWord, tailWord_4789616, baseEnd_4789616] using wordTrace_append hprefix tailTrace_4789616
  have hstable : (prefixWord ++ tailWord_4789616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789616).length < 2 ^ (prefixWord ++ tailWord_4789616).sum := by decide
  have hdescent : baseEnd_4789616 < baseStart_4789616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789656 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 2, 6]
def baseStart_4789656 : Nat := 118140960795 + 4789656 * 2 ^ 59
def prefixEnd_4789656 : Nat := 4983230072969 + 3 ^ 40 * 4789656 * 2
def baseEnd_4789656 : Nat := 819798565897072560857593

theorem tailTrace_4789656 : CollatzResearch.WordTrace tailWord_4789656 prefixEnd_4789656 819798565897072560857593 := by
  unfold tailWord_4789656
  simp only [CollatzResearch.WordTrace]
  refine ⟨87346552967950897482478411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116462070623934529976637881 87346552967950897482478411)
  ·
    refine ⟨131019829451926346223717617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87346552967950897482478411 131019829451926346223717617)
    ·
      refine ⟨98264872088944759667788213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131019829451926346223717617 98264872088944759667788213)
      ·
        refine ⟨9212331758338571218855145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98264872088944759667788213 9212331758338571218855145)
        ·
          refine ⟨6909248818753928414141359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9212331758338571218855145 6909248818753928414141359)
          ·
            refine ⟨10363873228130892621212039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6909248818753928414141359 10363873228130892621212039)
            ·
              refine ⟨15545809842196338931818059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10363873228130892621212039 15545809842196338931818059)
              ·
                refine ⟨23318714763294508397727089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15545809842196338931818059 23318714763294508397727089)
                ·
                  refine ⟨17489036072470881298295317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23318714763294508397727089 17489036072470881298295317)
                  ·
                    refine ⟨819798565897072560857593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17489036072470881298295317 819798565897072560857593)
                    ·
                      rfl

theorem cell23_4789656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_4789656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789656 prefixEnd_4789656 := by exact prefixLift 4789656
  have htrace : WordTrace (prefixWord ++ tailWord_4789656) baseStart_4789656 baseEnd_4789656 := by
    simpa [prefixWord, tailWord_4789656, baseEnd_4789656] using wordTrace_append hprefix tailTrace_4789656
  have hstable : (prefixWord ++ tailWord_4789656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789656).length < 2 ^ (prefixWord ++ tailWord_4789656).sum := by decide
  have hdescent : baseEnd_4789656 < baseStart_4789656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789663 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 1, 4, 2]
def baseStart_4789663 : Nat := 118140960795 + 4789663 * 2 ^ 59
def prefixEnd_4789663 : Nat := 4983230072969 + 3 ^ 40 * 4789663 * 2
def baseEnd_4789663 : Nat := 2459399292055799155185247

theorem tailTrace_4789663 : CollatzResearch.WordTrace tailWord_4789663 prefixEnd_4789663 2459399292055799155185247 := by
  unfold tailWord_4789663
  simp only [CollatzResearch.WordTrace]
  refine ⟨174693361246876435160461643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116462240831250956773641095 174693361246876435160461643)
  ·
    refine ⟨262040041870314652740692465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174693361246876435160461643 262040041870314652740692465)
    ·
      refine ⟨196530031402735989555519349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262040041870314652740692465 196530031402735989555519349)
      ·
        refine ⟨18424690444006499020829939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196530031402735989555519349 18424690444006499020829939)
        ·
          refine ⟨27637035666009748531244909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18424690444006499020829939 27637035666009748531244909)
          ·
            refine ⟨10363888374753655699216841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27637035666009748531244909 10363888374753655699216841)
            ·
              refine ⟨7772916281065241774412631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10363888374753655699216841 7772916281065241774412631)
              ·
                refine ⟨11659374421597862661618947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7772916281065241774412631 11659374421597862661618947)
                ·
                  refine ⟨17489061632396793992428421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11659374421597862661618947 17489061632396793992428421)
                  ·
                    refine ⟨3279199056074398873580329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17489061632396793992428421 3279199056074398873580329)
                    ·
                      refine ⟨2459399292055799155185247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279199056074398873580329 2459399292055799155185247)
                      ·
                        rfl

theorem cell23_4789663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_4789663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789663 prefixEnd_4789663 := by exact prefixLift 4789663
  have htrace : WordTrace (prefixWord ++ tailWord_4789663) baseStart_4789663 baseEnd_4789663 := by
    simpa [prefixWord, tailWord_4789663, baseEnd_4789663] using wordTrace_append hprefix tailTrace_4789663
  have hstable : (prefixWord ++ tailWord_4789663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789663).length < 2 ^ (prefixWord ++ tailWord_4789663).sum := by decide
  have hdescent : baseEnd_4789663 < baseStart_4789663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789699 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 2, 5]
def baseStart_4789699 : Nat := 118140960795 + 4789699 * 2 ^ 59
def prefixEnd_4789699 : Nat := 4983230072969 + 3 ^ 40 * 4789699 * 2
def baseEnd_4789699 : Nat := 819805925786453671445027

theorem tailTrace_4789699 : CollatzResearch.WordTrace tailWord_4789699 prefixEnd_4789699 819805925786453671445027 := by
  unfold tailWord_4789699
  simp only [CollatzResearch.WordTrace]
  refine ⟨174694674274746013308772151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116463116183164008872514767 174694674274746013308772151)
  ·
    refine ⟨262042011412119019963158227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174694674274746013308772151 262042011412119019963158227)
    ·
      refine ⟨393063017118178529944737341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262042011412119019963158227 393063017118178529944737341)
      ·
        refine ⟨147398631419316948729276503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393063017118178529944737341 147398631419316948729276503)
        ·
          refine ⟨221097947128975423093914755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147398631419316948729276503 221097947128975423093914755)
          ·
            refine ⟨331646920693463134640872133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221097947128975423093914755 331646920693463134640872133)
            ·
              refine ⟨62183797630024337745163525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 331646920693463134640872133 62183797630024337745163525)
              ·
                refine ⟨11659462055629563327218161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62183797630024337745163525 11659462055629563327218161)
                ·
                  refine ⟨8744596541722172495413621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11659462055629563327218161 8744596541722172495413621)
                  ·
                    refine ⟨819805925786453671445027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8744596541722172495413621 819805925786453671445027)
                    ·
                      rfl

theorem cell23_4789699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 5].length) (baseStart_4789699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789699 prefixEnd_4789699 := by exact prefixLift 4789699
  have htrace : WordTrace (prefixWord ++ tailWord_4789699) baseStart_4789699 baseEnd_4789699 := by
    simpa [prefixWord, tailWord_4789699, baseEnd_4789699] using wordTrace_append hprefix tailTrace_4789699
  have hstable : (prefixWord ++ tailWord_4789699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789699).length < 2 ^ (prefixWord ++ tailWord_4789699).sum := by decide
  have hdescent : baseEnd_4789699 < baseStart_4789699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789736 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4789736 : Nat := 118140960795 + 4789736 * 2 ^ 59
def prefixEnd_4789736 : Nat := 4983230072969 + 3 ^ 40 * 4789736 * 2
def baseEnd_4789736 : Nat := 2459436776143577369572411

theorem tailTrace_4789736 : CollatzResearch.WordTrace tailWord_4789736 prefixEnd_4789736 2459436776143577369572411 := by
  unfold tailWord_4789736
  simp only [CollatzResearch.WordTrace]
  refine ⟨87348011887805984313934531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116464015850407979085246041 87348011887805984313934531)
  ·
    refine ⟨131022017831708976470901797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87348011887805984313934531 131022017831708976470901797)
    ·
      refine ⟨24566628343445433088294087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131022017831708976470901797 24566628343445433088294087)
      ·
        refine ⟨36849942515168149632441131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24566628343445433088294087 36849942515168149632441131)
        ·
          refine ⟨55274913772752224448661697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36849942515168149632441131 55274913772752224448661697)
          ·
            refine ⟨41456185329564168336496273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55274913772752224448661697 41456185329564168336496273)
            ·
              refine ⟨31092138997173126252372205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41456185329564168336496273 31092138997173126252372205)
              ·
                refine ⟨11659552123939922344639577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31092138997173126252372205 11659552123939922344639577)
                ·
                  refine ⟨8744664092954941758479683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11659552123939922344639577 8744664092954941758479683)
                  ·
                    refine ⟨13116996139432412637719525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8744664092954941758479683 13116996139432412637719525)
                    ·
                      refine ⟨2459436776143577369572411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13116996139432412637719525 2459436776143577369572411)
                      ·
                        rfl

theorem cell23_4789736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4789736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789736 prefixEnd_4789736 := by exact prefixLift 4789736
  have htrace : WordTrace (prefixWord ++ tailWord_4789736) baseStart_4789736 baseEnd_4789736 := by
    simpa [prefixWord, tailWord_4789736, baseEnd_4789736] using wordTrace_append hprefix tailTrace_4789736
  have hstable : (prefixWord ++ tailWord_4789736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789736).length < 2 ^ (prefixWord ++ tailWord_4789736).sum := by decide
  have hdescent : baseEnd_4789736 < baseStart_4789736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789756 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_4789756 : Nat := 118140960795 + 4789756 * 2 ^ 59
def prefixEnd_4789756 : Nat := 4983230072969 + 3 ^ 40 * 4789756 * 2
def baseEnd_4789756 : Nat := 2459447045756667291322319

theorem tailTrace_4789756 : CollatzResearch.WordTrace tailWord_4789756 prefixEnd_4789756 2459447045756667291322319 := by
  unfold tailWord_4789756
  simp only [CollatzResearch.WordTrace]
  refine ⟨87348376617769756021798561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116464502157026341362398081 87348376617769756021798561)
  ·
    refine ⟨65511282463327317016348921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87348376617769756021798561 65511282463327317016348921)
    ·
      refine ⟨49133461847495487762261691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65511282463327317016348921 49133461847495487762261691)
      ·
        refine ⟨73700192771243231643392537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49133461847495487762261691 73700192771243231643392537)
        ·
          refine ⟨55275144578432423732544403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73700192771243231643392537 55275144578432423732544403)
          ·
            refine ⟨82912716867648635598816605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55275144578432423732544403 82912716867648635598816605)
            ·
              refine ⟨31092268825368238349556227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82912716867648635598816605 31092268825368238349556227)
              ·
                refine ⟨46638403238052357524334341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31092268825368238349556227 46638403238052357524334341)
                ·
                  refine ⟨8744700607134817035812689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46638403238052357524334341 8744700607134817035812689)
                  ·
                    refine ⟨6558525455351112776859517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8744700607134817035812689 6558525455351112776859517)
                    ·
                      refine ⟨2459447045756667291322319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6558525455351112776859517 2459447045756667291322319)
                      ·
                        rfl

theorem cell23_4789756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_4789756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789756 prefixEnd_4789756 := by exact prefixLift 4789756
  have htrace : WordTrace (prefixWord ++ tailWord_4789756) baseStart_4789756 baseEnd_4789756 := by
    simpa [prefixWord, tailWord_4789756, baseEnd_4789756] using wordTrace_append hprefix tailTrace_4789756
  have hstable : (prefixWord ++ tailWord_4789756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789756).length < 2 ^ (prefixWord ++ tailWord_4789756).sum := by decide
  have hdescent : baseEnd_4789756 < baseStart_4789756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789836 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_4789836 : Nat := 118140960795 + 4789836 * 2 ^ 59
def prefixEnd_4789836 : Nat := 4983230072969 + 3 ^ 40 * 4789836 * 2
def baseEnd_4789836 : Nat := 819829374736342326107317

theorem tailTrace_4789836 : CollatzResearch.WordTrace tailWord_4789836 prefixEnd_4789836 819829374736342326107317 := by
  unfold tailWord_4789836
  simp only [CollatzResearch.WordTrace]
  refine ⟨87349835537624842853254681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116466447383499790471006241 87349835537624842853254681)
  ·
    refine ⟨65512376653218632139941011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87349835537624842853254681 65512376653218632139941011)
    ·
      refine ⟨98268564979827948209911517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65512376653218632139941011 98268564979827948209911517)
      ·
        refine ⟨36850711867435480578716819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98268564979827948209911517 36850711867435480578716819)
        ·
          refine ⟨55276067801153220868075229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36850711867435480578716819 55276067801153220868075229)
          ·
            refine ⟨20728525425432457825528211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55276067801153220868075229 20728525425432457825528211)
            ·
              refine ⟨31092788138148686738292317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20728525425432457825528211 31092788138148686738292317)
              ·
                refine ⟨11659795551805757526859619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31092788138148686738292317 11659795551805757526859619)
                ·
                  refine ⟨17489693327708636290289429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11659795551805757526859619 17489693327708636290289429)
                  ·
                    refine ⟨819829374736342326107317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17489693327708636290289429 819829374736342326107317)
                    ·
                      rfl

theorem cell23_4789836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_4789836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789836 prefixEnd_4789836 := by exact prefixLift 4789836
  have htrace : WordTrace (prefixWord ++ tailWord_4789836) baseStart_4789836 baseEnd_4789836 := by
    simpa [prefixWord, tailWord_4789836, baseEnd_4789836] using wordTrace_append hprefix tailTrace_4789836
  have hstable : (prefixWord ++ tailWord_4789836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789836).length < 2 ^ (prefixWord ++ tailWord_4789836).sum := by decide
  have hdescent : baseEnd_4789836 < baseStart_4789836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789837 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_4789837 : Nat := 118140960795 + 4789837 * 2 ^ 59
def prefixEnd_4789837 : Nat := 4983230072969 + 3 ^ 40 * 4789837 * 2
def baseEnd_4789837 : Nat := 2459488637689681474409447

theorem tailTrace_4789837 : CollatzResearch.WordTrace tailWord_4789837 prefixEnd_4789837 2459488637689681474409447 := by
  unfold tailWord_4789837
  simp only [CollatzResearch.WordTrace]
  refine ⟨174699707548246062877295765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116466471698830708584863843 174699707548246062877295765)
  ·
    refine ⟨8189048791324034197373239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174699707548246062877295765 8189048791324034197373239)
    ·
      refine ⟨12283573186986051296059859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8189048791324034197373239 12283573186986051296059859)
      ·
        refine ⟨18425359780479076944089789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12283573186986051296059859 18425359780479076944089789)
        ·
          refine ⟨6909509917679653854033671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18425359780479076944089789 6909509917679653854033671)
          ·
            refine ⟨10364264876519480781050507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6909509917679653854033671 10364264876519480781050507)
            ·
              refine ⟨15546397314779221171575761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10364264876519480781050507 15546397314779221171575761)
              ·
                refine ⟨11659797986084415878681821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15546397314779221171575761 11659797986084415878681821)
                ·
                  refine ⟨4372424244781655954505683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11659797986084415878681821 4372424244781655954505683)
                  ·
                    refine ⟨6558636367172483931758525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4372424244781655954505683 6558636367172483931758525)
                    ·
                      refine ⟨2459488637689681474409447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6558636367172483931758525 2459488637689681474409447)
                      ·
                        rfl

theorem cell23_4789837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_4789837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789837 prefixEnd_4789837 := by exact prefixLift 4789837
  have htrace : WordTrace (prefixWord ++ tailWord_4789837) baseStart_4789837 baseEnd_4789837 := by
    simpa [prefixWord, tailWord_4789837, baseEnd_4789837] using wordTrace_append hprefix tailTrace_4789837
  have hstable : (prefixWord ++ tailWord_4789837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789837).length < 2 ^ (prefixWord ++ tailWord_4789837).sum := by decide
  have hdescent : baseEnd_4789837 < baseStart_4789837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789849 : List Nat := [1, 2, 1, 2, 2, 1, 1, 13]
def baseStart_4789849 : Nat := 118140960795 + 4789849 * 2 ^ 59
def prefixEnd_4789849 : Nat := 4983230072969 + 3 ^ 40 * 4789849 * 2
def baseEnd_4789849 : Nat := 91092399979908719535533

theorem tailTrace_4789849 : CollatzResearch.WordTrace tailWord_4789849 prefixEnd_4789849 91092399979908719535533 := by
  unfold tailWord_4789849
  simp only [CollatzResearch.WordTrace]
  refine ⟨174700145224202588926732601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116466763482801725951155067 174700145224202588926732601)
  ·
    refine ⟨131025108918151941695049451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174700145224202588926732601 131025108918151941695049451)
    ·
      refine ⟨196537663377227912542574177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131025108918151941695049451 196537663377227912542574177)
      ·
        refine ⟨147403247532920934406930633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196537663377227912542574177 147403247532920934406930633)
        ·
          refine ⟨110552435649690700805197975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147403247532920934406930633 110552435649690700805197975)
          ·
            refine ⟨165828653474536051207796963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110552435649690700805197975 165828653474536051207796963)
            ·
              refine ⟨248742980211804076811695445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165828653474536051207796963 248742980211804076811695445)
              ·
                refine ⟨91092399979908719535533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 248742980211804076811695445 91092399979908719535533)
                ·
                  rfl

theorem cell23_4789849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 13].length) (baseStart_4789849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789849 prefixEnd_4789849 := by exact prefixLift 4789849
  have htrace : WordTrace (prefixWord ++ tailWord_4789849) baseStart_4789849 baseEnd_4789849 := by
    simpa [prefixWord, tailWord_4789849, baseEnd_4789849] using wordTrace_append hprefix tailTrace_4789849
  have hstable : (prefixWord ++ tailWord_4789849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789849).length < 2 ^ (prefixWord ++ tailWord_4789849).sum := by decide
  have hdescent : baseEnd_4789849 < baseStart_4789849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789860 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_4789860 : Nat := 118140960795 + 4789860 * 2 ^ 59
def prefixEnd_4789860 : Nat := 4983230072969 + 3 ^ 40 * 4789860 * 2
def baseEnd_4789860 : Nat := 2459500447744734884421841

theorem tailTrace_4789860 : CollatzResearch.WordTrace tailWord_4789860 prefixEnd_4789860 2459500447744734884421841 := by
  unfold tailWord_4789860
  simp only [CollatzResearch.WordTrace]
  refine ⟨87350273213581368902691517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116467030951441825203588689 87350273213581368902691517)
  ·
    refine ⟨32756352455093013338509319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87350273213581368902691517 32756352455093013338509319)
    ·
      refine ⟨49134528682639520007763979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32756352455093013338509319 49134528682639520007763979)
      ·
        refine ⟨73701793023959280011645969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49134528682639520007763979 73701793023959280011645969)
        ·
          refine ⟨55276344767969460008734477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73701793023959280011645969 55276344767969460008734477)
          ·
            refine ⟨20728629287988547503275429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55276344767969460008734477 20728629287988547503275429)
            ·
              refine ⟨3886617991497852656864143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20728629287988547503275429 3886617991497852656864143)
              ·
                refine ⟨5829926987246778985296215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886617991497852656864143 5829926987246778985296215)
                ·
                  refine ⟨8744890480870168477944323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5829926987246778985296215 8744890480870168477944323)
                  ·
                    refine ⟨13117335721305252716916485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8744890480870168477944323 13117335721305252716916485)
                    ·
                      refine ⟨2459500447744734884421841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13117335721305252716916485 2459500447744734884421841)
                      ·
                        rfl

theorem cell23_4789860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_4789860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789860 prefixEnd_4789860 := by exact prefixLift 4789860
  have htrace : WordTrace (prefixWord ++ tailWord_4789860) baseStart_4789860 baseEnd_4789860 := by
    simpa [prefixWord, tailWord_4789860, baseEnd_4789860] using wordTrace_append hprefix tailTrace_4789860
  have hstable : (prefixWord ++ tailWord_4789860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789860).length < 2 ^ (prefixWord ++ tailWord_4789860).sum := by decide
  have hdescent : baseEnd_4789860 < baseStart_4789860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789866 : List Nat := [3, 1, 3, 2, 1, 3, 10]
def baseStart_4789866 : Nat := 118140960795 + 4789866 * 2 ^ 59
def prefixEnd_4789866 : Nat := 4983230072969 + 3 ^ 40 * 4789866 * 2
def baseEnd_4789866 : Nat := 30364241094181010628973

theorem tailTrace_4789866 : CollatzResearch.WordTrace tailWord_4789866 prefixEnd_4789866 30364241094181010628973 := by
  unfold tailWord_4789866
  simp only [CollatzResearch.WordTrace]
  refine ⟨43675191316285250207525363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116467176843427333886734301 43675191316285250207525363)
  ·
    refine ⟨65512786974427875311288045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43675191316285250207525363 65512786974427875311288045)
    ·
      refine ⟨24567295115410453241733017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65512786974427875311288045 24567295115410453241733017)
      ·
        refine ⟨18425471336557839931299763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24567295115410453241733017 18425471336557839931299763)
        ·
          refine ⟨27638207004836759896949645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18425471336557839931299763 27638207004836759896949645)
          ·
            refine ⟨10364327626813784961356117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27638207004836759896949645 10364327626813784961356117)
            ·
              refine ⟨30364241094181010628973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10364327626813784961356117 30364241094181010628973)
              ·
                rfl

theorem cell23_4789866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 10].length) (baseStart_4789866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789866 prefixEnd_4789866 := by exact prefixLift 4789866
  have htrace : WordTrace (prefixWord ++ tailWord_4789866) baseStart_4789866 baseEnd_4789866 := by
    simpa [prefixWord, tailWord_4789866, baseEnd_4789866] using wordTrace_append hprefix tailTrace_4789866
  have hstable : (prefixWord ++ tailWord_4789866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789866).length < 2 ^ (prefixWord ++ tailWord_4789866).sum := by decide
  have hdescent : baseEnd_4789866 < baseStart_4789866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789870 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_4789870 : Nat := 118140960795 + 4789870 * 2 ^ 59
def prefixEnd_4789870 : Nat := 4983230072969 + 3 ^ 40 * 4789870 * 2
def baseEnd_4789870 : Nat := 819835194183759948432265

theorem tailTrace_4789870 : CollatzResearch.WordTrace tailWord_4789870 prefixEnd_4789870 819835194183759948432265 := by
  unfold tailWord_4789870
  simp only [CollatzResearch.WordTrace]
  refine ⟨21837613894640813689155883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116467274104751006342164709 21837613894640813689155883)
  ·
    refine ⟨32756420841961220533733825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21837613894640813689155883 32756420841961220533733825)
    ·
      refine ⟨24567315631470915400300369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32756420841961220533733825 24567315631470915400300369)
      ·
        refine ⟨18425486723603186550225277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24567315631470915400300369 18425486723603186550225277)
        ·
          refine ⟨6909557521351194956334479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18425486723603186550225277 6909557521351194956334479)
          ·
            refine ⟨10364336282026792434501719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6909557521351194956334479 10364336282026792434501719)
            ·
              refine ⟨15546504423040188651752579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10364336282026792434501719 15546504423040188651752579)
              ·
                refine ⟨23319756634560282977628869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15546504423040188651752579 23319756634560282977628869)
                ·
                  refine ⟨4372454368980053058305413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23319756634560282977628869 4372454368980053058305413)
                  ·
                    refine ⟨819835194183759948432265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4372454368980053058305413 819835194183759948432265)
                    ·
                      rfl

theorem cell23_4789870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_4789870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789870 prefixEnd_4789870 := by exact prefixLift 4789870
  have htrace : WordTrace (prefixWord ++ tailWord_4789870) baseStart_4789870 baseEnd_4789870 := by
    simpa [prefixWord, tailWord_4789870, baseEnd_4789870] using wordTrace_append hprefix tailTrace_4789870
  have hstable : (prefixWord ++ tailWord_4789870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789870).length < 2 ^ (prefixWord ++ tailWord_4789870).sum := by decide
  have hdescent : baseEnd_4789870 < baseStart_4789870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789877 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4789877 : Nat := 118140960795 + 4789877 * 2 ^ 59
def prefixEnd_4789877 : Nat := 4983230072969 + 3 ^ 40 * 4789877 * 2
def baseEnd_4789877 : Nat := 2459509176915861317909263

theorem tailTrace_4789877 : CollatzResearch.WordTrace tailWord_4789877 prefixEnd_4789877 2459509176915861317909263 := by
  unfold tailWord_4789877
  simp only [CollatzResearch.WordTrace]
  refine ⟨174701166468101149708751885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116467444312067433139167923 174701166468101149708751885)
  ·
    refine ⟨65512937425537931140781957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174701166468101149708751885 65512937425537931140781957)
    ·
      refine ⟨12283675767288362088896617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65512937425537931140781957 12283675767288362088896617)
      ·
        refine ⟨9212756825466271566672463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12283675767288362088896617 9212756825466271566672463)
        ·
          refine ⟨13819135238199407350008695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9212756825466271566672463 13819135238199407350008695)
          ·
            refine ⟨20728702857299111025013043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13819135238199407350008695 20728702857299111025013043)
            ·
              refine ⟨31093054285948666537519565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20728702857299111025013043 31093054285948666537519565)
              ·
                refine ⟨11659895357230749951569837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31093054285948666537519565 11659895357230749951569837)
                ·
                  refine ⟨4372460758961531231838689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11659895357230749951569837 4372460758961531231838689)
                  ·
                    refine ⟨3279345569221148423879017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4372460758961531231838689 3279345569221148423879017)
                    ·
                      refine ⟨2459509176915861317909263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279345569221148423879017 2459509176915861317909263)
                      ·
                        rfl

theorem cell23_4789877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4789877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789877 prefixEnd_4789877 := by exact prefixLift 4789877
  have htrace : WordTrace (prefixWord ++ tailWord_4789877) baseStart_4789877 baseEnd_4789877 := by
    simpa [prefixWord, tailWord_4789877, baseEnd_4789877] using wordTrace_append hprefix tailTrace_4789877
  have hstable : (prefixWord ++ tailWord_4789877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789877).length < 2 ^ (prefixWord ++ tailWord_4789877).sum := by decide
  have hdescent : baseEnd_4789877 < baseStart_4789877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789928 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4789928 : Nat := 118140960795 + 4789928 * 2 ^ 59
def prefixEnd_4789928 : Nat := 4983230072969 + 3 ^ 40 * 4789928 * 2
def baseEnd_4789928 : Nat := 2459535364429240618371529

theorem tailTrace_4789928 : CollatzResearch.WordTrace tailWord_4789928 prefixEnd_4789928 2459535364429240618371529 := by
  unfold tailWord_4789928
  simp only [CollatzResearch.WordTrace]
  refine ⟨87351513295458192709429219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116468684393944256945905625 87351513295458192709429219)
  ·
    refine ⟨131027269943187289064143829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87351513295458192709429219 131027269943187289064143829)
    ·
      refine ⟨3070951639293452087440871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131027269943187289064143829 3070951639293452087440871)
      ·
        refine ⟨4606427458940178131161307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070951639293452087440871 4606427458940178131161307)
        ·
          refine ⟨6909641188410267196741961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606427458940178131161307 6909641188410267196741961)
          ·
            refine ⟨5182230891307700397556471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6909641188410267196741961 5182230891307700397556471)
            ·
              refine ⟨7773346336961550596334707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182230891307700397556471 7773346336961550596334707)
              ·
                refine ⟨11660019505442325894502061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773346336961550596334707 11660019505442325894502061)
                ·
                  refine ⟨4372507314540872210438273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11660019505442325894502061 4372507314540872210438273)
                  ·
                    refine ⟨3279380485905654157828705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4372507314540872210438273 3279380485905654157828705)
                    ·
                      refine ⟨2459535364429240618371529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279380485905654157828705 2459535364429240618371529)
                      ·
                        rfl

theorem cell23_4789928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4789928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789928 prefixEnd_4789928 := by exact prefixLift 4789928
  have htrace : WordTrace (prefixWord ++ tailWord_4789928) baseStart_4789928 baseEnd_4789928 := by
    simpa [prefixWord, tailWord_4789928, baseEnd_4789928] using wordTrace_append hprefix tailTrace_4789928
  have hstable : (prefixWord ++ tailWord_4789928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789928).length < 2 ^ (prefixWord ++ tailWord_4789928).sum := by decide
  have hdescent : baseEnd_4789928 < baseStart_4789928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789933 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4789933 : Nat := 118140960795 + 4789933 * 2 ^ 59
def prefixEnd_4789933 : Nat := 4983230072969 + 3 ^ 40 * 4789933 * 2
def baseEnd_4789933 : Nat := 2459537931832513098809005

theorem tailTrace_4789933 : CollatzResearch.WordTrace tailWord_4789933 prefixEnd_4789933 2459537931832513098809005 := by
  unfold tailWord_4789933
  simp only [CollatzResearch.WordTrace]
  refine ⟨174703208955898271272790453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116468805970598847515193635 174703208955898271272790453)
  ·
    refine ⟨16378425839615462931824105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174703208955898271272790453 16378425839615462931824105)
    ·
      refine ⟨12283819379711597198868079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16378425839615462931824105 12283819379711597198868079)
      ·
        refine ⟨18425729069567395798302119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12283819379711597198868079 18425729069567395798302119)
        ·
          refine ⟨27638593604351093697453179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18425729069567395798302119 27638593604351093697453179)
          ·
            refine ⟨41457890406526640546179769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27638593604351093697453179 41457890406526640546179769)
            ·
              refine ⟨31093417804894980409634827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41457890406526640546179769 31093417804894980409634827)
              ·
                refine ⟨46640126707342470614452241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31093417804894980409634827 46640126707342470614452241)
                ·
                  refine ⟨34980095030506852960839181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46640126707342470614452241 34980095030506852960839181)
                  ·
                    refine ⟨13117535636440069860314693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34980095030506852960839181 13117535636440069860314693)
                    ·
                      refine ⟨2459537931832513098809005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13117535636440069860314693 2459537931832513098809005)
                      ·
                        rfl

theorem cell23_4789933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4789933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789933 prefixEnd_4789933 := by exact prefixLift 4789933
  have htrace : WordTrace (prefixWord ++ tailWord_4789933) baseStart_4789933 baseEnd_4789933 := by
    simpa [prefixWord, tailWord_4789933, baseEnd_4789933] using wordTrace_append hprefix tailTrace_4789933
  have hstable : (prefixWord ++ tailWord_4789933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789933).length < 2 ^ (prefixWord ++ tailWord_4789933).sum := by decide
  have hdescent : baseEnd_4789933 < baseStart_4789933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789983 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 3]
def baseStart_4789983 : Nat := 118140960795 + 4789983 * 2 ^ 59
def prefixEnd_4789983 : Nat := 4983230072969 + 3 ^ 40 * 4789983 * 2
def baseEnd_4789983 : Nat := 2459563605865237903183775

theorem tailTrace_4789983 : CollatzResearch.WordTrace tailWord_4789983 prefixEnd_4789983 2459563605865237903183775 := by
  unfold tailWord_4789983
  simp only [CollatzResearch.WordTrace]
  refine ⟨174705032605717129812110603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116470021737144753208073735 174705032605717129812110603)
  ·
    refine ⟨262057548908575694718165905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174705032605717129812110603 262057548908575694718165905)
    ·
      refine ⟨196543161681431771038624429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262057548908575694718165905 196543161681431771038624429)
      ·
        refine ⟨73703685630536914139484161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196543161681431771038624429 73703685630536914139484161)
        ·
          refine ⟨55277764222902685604613121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73703685630536914139484161 55277764222902685604613121)
          ·
            refine ⟨41458323167177014203459841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55277764222902685604613121 41458323167177014203459841)
            ·
              refine ⟨31093742375382760652594881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41458323167177014203459841 31093742375382760652594881)
              ·
                refine ⟨23320306781537070489446161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31093742375382760652594881 23320306781537070489446161)
                ·
                  refine ⟨17490230086152802867084621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23320306781537070489446161 17490230086152802867084621)
                  ·
                    refine ⟨6558836282307301075156733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17490230086152802867084621 6558836282307301075156733)
                    ·
                      refine ⟨2459563605865237903183775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6558836282307301075156733 2459563605865237903183775)
                      ·
                        rfl

theorem cell23_4789983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_4789983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4789983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4789983 prefixEnd_4789983 := by exact prefixLift 4789983
  have htrace : WordTrace (prefixWord ++ tailWord_4789983) baseStart_4789983 baseEnd_4789983 := by
    simpa [prefixWord, tailWord_4789983, baseEnd_4789983] using wordTrace_append hprefix tailTrace_4789983
  have hstable : (prefixWord ++ tailWord_4789983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789983).length < 2 ^ (prefixWord ++ tailWord_4789983).sum := by decide
  have hdescent : baseEnd_4789983 < baseStart_4789983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790016 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 2, 8]
def baseStart_4790016 : Nat := 118140960795 + 4790016 * 2 ^ 59
def prefixEnd_4790016 : Nat := 4983230072969 + 3 ^ 40 * 4790016 * 2
def baseEnd_4790016 : Nat := 819860183575612091357041

theorem tailTrace_4790016 : CollatzResearch.WordTrace tailWord_4790016 prefixEnd_4790016 819860183575612091357041 := by
  unfold tailWord_4790016
  simp only [CollatzResearch.WordTrace]
  refine ⟨87353118107298788224030951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116470824143065050965374601 87353118107298788224030951)
  ·
    refine ⟨131029677160948182336046427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87353118107298788224030951 131029677160948182336046427)
    ·
      refine ⟨196544515741422273504069641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131029677160948182336046427 196544515741422273504069641)
      ·
        refine ⟨147408386806066705128052231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196544515741422273504069641 147408386806066705128052231)
        ·
          refine ⟨221112580209100057692078347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147408386806066705128052231 221112580209100057692078347)
          ·
            refine ⟨331668870313650086538117521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221112580209100057692078347 331668870313650086538117521)
            ·
              refine ⟨248751652735237564903588141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331668870313650086538117521 248751652735237564903588141)
              ·
                refine ⟨93281869775714086838845553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248751652735237564903588141 93281869775714086838845553)
                ·
                  refine ⟨69961402331785565129134165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93281869775714086838845553 69961402331785565129134165)
                  ·
                    refine ⟨819860183575612091357041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69961402331785565129134165 819860183575612091357041)
                    ·
                      rfl

theorem cell23_4790016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_4790016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790016 prefixEnd_4790016 := by exact prefixLift 4790016
  have htrace : WordTrace (prefixWord ++ tailWord_4790016) baseStart_4790016 baseEnd_4790016 := by
    simpa [prefixWord, tailWord_4790016, baseEnd_4790016] using wordTrace_append hprefix tailTrace_4790016
  have hstable : (prefixWord ++ tailWord_4790016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790016).length < 2 ^ (prefixWord ++ tailWord_4790016).sum := by decide
  have hdescent : baseEnd_4790016 < baseStart_4790016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790020 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_4790020 : Nat := 118140960795 + 4790020 * 2 ^ 59
def prefixEnd_4790020 : Nat := 4983230072969 + 3 ^ 40 * 4790020 * 2
def baseEnd_4790020 : Nat := 819860868216484752807035

theorem tailTrace_4790020 : CollatzResearch.WordTrace tailWord_4790020 prefixEnd_4790020 819860868216484752807035 := by
  unfold tailWord_4790020
  simp only [CollatzResearch.WordTrace]
  refine ⟨87353191053291542565603757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116470921404388723420805009 87353191053291542565603757)
  ·
    refine ⟨32757446644984328462101409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87353191053291542565603757 32757446644984328462101409)
    ·
      refine ⟨24568084983738246346576057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32757446644984328462101409 24568084983738246346576057)
      ·
        refine ⟨18426063737803684759932043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24568084983738246346576057 18426063737803684759932043)
        ·
          refine ⟨27639095606705527139898065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18426063737803684759932043 27639095606705527139898065)
          ·
            refine ⟨20729321705029145354923549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27639095606705527139898065 20729321705029145354923549)
            ·
              refine ⟨7773495639385929508096331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20729321705029145354923549 7773495639385929508096331)
              ·
                refine ⟨11660243459078894262144497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773495639385929508096331 11660243459078894262144497)
                ·
                  refine ⟨8745182594309170696608373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11660243459078894262144497 8745182594309170696608373)
                  ·
                    refine ⟨819860868216484752807035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8745182594309170696608373 819860868216484752807035)
                    ·
                      rfl

theorem cell23_4790020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_4790020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790020 prefixEnd_4790020 := by exact prefixLift 4790020
  have htrace : WordTrace (prefixWord ++ tailWord_4790020) baseStart_4790020 baseEnd_4790020 := by
    simpa [prefixWord, tailWord_4790020, baseEnd_4790020] using wordTrace_append hprefix tailTrace_4790020
  have hstable : (prefixWord ++ tailWord_4790020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790020).length < 2 ^ (prefixWord ++ tailWord_4790020).sum := by decide
  have hdescent : baseEnd_4790020 < baseStart_4790020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790033 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 7, 4]
def baseStart_4790033 : Nat := 118140960795 + 4790033 * 2 ^ 59
def prefixEnd_4790033 : Nat := 4983230072969 + 3 ^ 40 * 4790033 * 2
def baseEnd_4790033 : Nat := 819863093299320902519515

theorem tailTrace_4790033 : CollatzResearch.WordTrace tailWord_4790033 prefixEnd_4790033 819863093299320902519515 := by
  unfold tailWord_4790033
  simp only [CollatzResearch.WordTrace]
  refine ⟨174706856255535988351430753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116471237503690658900953835 174706856255535988351430753)
  ·
    refine ⟨131030142191651991263573065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174706856255535988351430753 131030142191651991263573065)
    ·
      refine ⟨98272606643738993447679799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131030142191651991263573065 98272606643738993447679799)
      ·
        refine ⟨147408909965608490171519699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98272606643738993447679799 147408909965608490171519699)
        ·
          refine ⟨221113364948412735257279549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147408909965608490171519699 221113364948412735257279549)
          ·
            refine ⟨82917511855654775721479831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221113364948412735257279549 82917511855654775721479831)
            ·
              refine ⟨124376267783482163582219747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82917511855654775721479831 124376267783482163582219747)
              ·
                refine ⟨186564401675223245373329621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124376267783482163582219747 186564401675223245373329621)
                ·
                  refine ⟨4372603164263044813437413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 186564401675223245373329621 4372603164263044813437413)
                  ·
                    refine ⟨819863093299320902519515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4372603164263044813437413 819863093299320902519515)
                    ·
                      rfl

theorem cell23_4790033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_4790033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790033 prefixEnd_4790033 := by exact prefixLift 4790033
  have htrace : WordTrace (prefixWord ++ tailWord_4790033) baseStart_4790033 baseEnd_4790033 := by
    simpa [prefixWord, tailWord_4790033, baseEnd_4790033] using wordTrace_append hprefix tailTrace_4790033
  have hstable : (prefixWord ++ tailWord_4790033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790033).length < 2 ^ (prefixWord ++ tailWord_4790033).sum := by decide
  have hdescent : baseEnd_4790033 < baseStart_4790033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790040 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 2, 4, 2]
def baseStart_4790040 : Nat := 118140960795 + 4790040 * 2 ^ 59
def prefixEnd_4790040 : Nat := 4983230072969 + 3 ^ 40 * 4790040 * 2
def baseEnd_4790040 : Nat := 2459592874262544180171013

theorem tailTrace_4790040 : CollatzResearch.WordTrace tailWord_4790040 prefixEnd_4790040 2459592874262544180171013 := by
  unfold tailWord_4790040
  simp only [CollatzResearch.WordTrace]
  refine ⟨87353555783255314273467787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116471407711007085697957049 87353555783255314273467787)
  ·
    refine ⟨131030333674882971410201681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87353555783255314273467787 131030333674882971410201681)
    ·
      refine ⟨98272750256162228557651261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131030333674882971410201681 98272750256162228557651261)
      ·
        refine ⟨36852281346060835709119223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98272750256162228557651261 36852281346060835709119223)
        ·
          refine ⟨55278422019091253563678835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36852281346060835709119223 55278422019091253563678835)
          ·
            refine ⟨82917633028636880345518253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55278422019091253563678835 82917633028636880345518253)
            ·
              refine ⟨31094112385738830129569345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82917633028636880345518253 31094112385738830129569345)
              ·
                refine ⟨23320584289304122597177009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31094112385738830129569345 23320584289304122597177009)
                ·
                  refine ⟨17490438216978091947882757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23320584289304122597177009 17490438216978091947882757)
                  ·
                    refine ⟨3279457165683392240228017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17490438216978091947882757 3279457165683392240228017)
                    ·
                      refine ⟨2459592874262544180171013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279457165683392240228017 2459592874262544180171013)
                      ·
                        rfl

theorem cell23_4790040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_4790040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790040 prefixEnd_4790040 := by exact prefixLift 4790040
  have htrace : WordTrace (prefixWord ++ tailWord_4790040) baseStart_4790040 baseEnd_4790040 := by
    simpa [prefixWord, tailWord_4790040, baseEnd_4790040] using wordTrace_append hprefix tailTrace_4790040
  have hstable : (prefixWord ++ tailWord_4790040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790040).length < 2 ^ (prefixWord ++ tailWord_4790040).sum := by decide
  have hdescent : baseEnd_4790040 < baseStart_4790040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790114 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 6]
def baseStart_4790114 : Nat := 118140960795 + 4790114 * 2 ^ 59
def prefixEnd_4790114 : Nat := 4983230072969 + 3 ^ 40 * 4790114 * 2
def baseEnd_4790114 : Nat := 273292319092330765627297

theorem tailTrace_4790114 : CollatzResearch.WordTrace tailWord_4790114 prefixEnd_4790114 273292319092330765627297 := by
  unfold tailWord_4790114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43677452642060634796282349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116473207045495026123419597 43677452642060634796282349)
  ·
    refine ⟨16379044740772738048605881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43677452642060634796282349 16379044740772738048605881)
    ·
      refine ⟨12284283555579553536454411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16379044740772738048605881 12284283555579553536454411)
      ·
        refine ⟨18426425333369330304681617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12284283555579553536454411 18426425333369330304681617)
        ·
          refine ⟨13819819000026997728511213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18426425333369330304681617 13819819000026997728511213)
          ·
            refine ⟨5182432125010124148191705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13819819000026997728511213 5182432125010124148191705)
            ·
              refine ⟨3886824093757593111143779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5182432125010124148191705 3886824093757593111143779)
              ·
                refine ⟨5830236140636389666715669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886824093757593111143779 5830236140636389666715669)
                ·
                  refine ⟨273292319092330765627297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5830236140636389666715669 273292319092330765627297)
                  ·
                    rfl

theorem cell23_4790114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_4790114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790114 prefixEnd_4790114 := by exact prefixLift 4790114
  have htrace : WordTrace (prefixWord ++ tailWord_4790114) baseStart_4790114 baseEnd_4790114 := by
    simpa [prefixWord, tailWord_4790114, baseEnd_4790114] using wordTrace_append hprefix tailTrace_4790114
  have hstable : (prefixWord ++ tailWord_4790114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790114).length < 2 ^ (prefixWord ++ tailWord_4790114).sum := by decide
  have hdescent : baseEnd_4790114 < baseStart_4790114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790123 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 1, 6]
def baseStart_4790123 : Nat := 118140960795 + 4790123 * 2 ^ 59
def prefixEnd_4790123 : Nat := 4983230072969 + 3 ^ 40 * 4790123 * 2
def baseEnd_4790123 : Nat := 819878497718955785144377

theorem tailTrace_4790123 : CollatzResearch.WordTrace tailWord_4790123 prefixEnd_4790123 819878497718955785144377 := by
  unfold tailWord_4790123
  simp only [CollatzResearch.WordTrace]
  refine ⟨174710138825209933722207023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116473425883473289148138015 174710138825209933722207023)
  ·
    refine ⟨262065208237814900583310535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174710138825209933722207023 262065208237814900583310535)
    ·
      refine ⟨393097812356722350874965803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262065208237814900583310535 393097812356722350874965803)
      ·
        refine ⟨589646718535083526312448705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393097812356722350874965803 589646718535083526312448705)
        ·
          refine ⟨442235038901312644734336529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589646718535083526312448705 442235038901312644734336529)
          ·
            refine ⟨331676279175984483550752397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442235038901312644734336529 331676279175984483550752397)
            ·
              refine ⟨124378604690994181331532149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 331676279175984483550752397 124378604690994181331532149)
              ·
                refine ⟨11660494189780704499831139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124378604690994181331532149 11660494189780704499831139)
                ·
                  refine ⟨17490741284671056749746709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11660494189780704499831139 17490741284671056749746709)
                  ·
                    refine ⟨819878497718955785144377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17490741284671056749746709 819878497718955785144377)
                    ·
                      rfl

theorem cell23_4790123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 6].length) (baseStart_4790123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790123 prefixEnd_4790123 := by exact prefixLift 4790123
  have htrace : WordTrace (prefixWord ++ tailWord_4790123) baseStart_4790123 baseEnd_4790123 := by
    simpa [prefixWord, tailWord_4790123, baseEnd_4790123] using wordTrace_append hprefix tailTrace_4790123
  have hstable : (prefixWord ++ tailWord_4790123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790123).length < 2 ^ (prefixWord ++ tailWord_4790123).sum := by decide
  have hdescent : baseEnd_4790123 < baseStart_4790123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790158 : List Nat := [4, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4790158 : Nat := 118140960795 + 4790158 * 2 ^ 59
def prefixEnd_4790158 : Nat := 4983230072969 + 3 ^ 40 * 4790158 * 2
def baseEnd_4790158 : Nat := 2459653464979774718495471

theorem tailTrace_4790158 : CollatzResearch.WordTrace tailWord_4790158 prefixEnd_4790158 2459653464979774718495471 := by
  unfold tailWord_4790158
  simp only [CollatzResearch.WordTrace]
  refine ⟨21838926922510391837466391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116474276920055423133154085 21838926922510391837466391)
  ·
    refine ⟨32758390383765587756199587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21838926922510391837466391 32758390383765587756199587)
    ·
      refine ⟨49137585575648381634299381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32758390383765587756199587 49137585575648381634299381)
      ·
        refine ⟨4606648647717035778215567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49137585575648381634299381 4606648647717035778215567)
        ·
          refine ⟨6909972971575553667323351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606648647717035778215567 6909972971575553667323351)
          ·
            refine ⟨10364959457363330500985027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6909972971575553667323351 10364959457363330500985027)
            ·
              refine ⟨15547439186044995751477541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10364959457363330500985027 15547439186044995751477541)
              ·
                refine ⟨2915144847383436703402039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15547439186044995751477541 2915144847383436703402039)
                ·
                  refine ⟨4372717271075155055103059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915144847383436703402039 4372717271075155055103059)
                  ·
                    refine ⟨6559075906612732582654589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4372717271075155055103059 6559075906612732582654589)
                    ·
                      refine ⟨2459653464979774718495471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559075906612732582654589 2459653464979774718495471)
                      ·
                        rfl

theorem cell23_4790158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4790158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790158 prefixEnd_4790158 := by exact prefixLift 4790158
  have htrace : WordTrace (prefixWord ++ tailWord_4790158) baseStart_4790158 baseEnd_4790158 := by
    simpa [prefixWord, tailWord_4790158, baseEnd_4790158] using wordTrace_append hprefix tailTrace_4790158
  have hstable : (prefixWord ++ tailWord_4790158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790158).length < 2 ^ (prefixWord ++ tailWord_4790158).sum := by decide
  have hdescent : baseEnd_4790158 < baseStart_4790158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790170 : List Nat := [3, 1, 1, 4, 2, 1, 3, 8]
def baseStart_4790170 : Nat := 118140960795 + 4790170 * 2 ^ 59
def prefixEnd_4790170 : Nat := 4983230072969 + 3 ^ 40 * 4790170 * 2
def baseEnd_4790170 : Nat := 91098504694356617464645

theorem tailTrace_4790170 : CollatzResearch.WordTrace tailWord_4790170 prefixEnd_4790170 91098504694356617464645 := by
  unfold tailWord_4790170
  simp only [CollatzResearch.WordTrace]
  refine ⟨43677963264009915187291991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116474568704026440499445309 43677963264009915187291991)
  ·
    refine ⟨65516944896014872780937987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43677963264009915187291991 65516944896014872780937987)
    ·
      refine ⟨98275417344022309171406981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65516944896014872780937987 98275417344022309171406981)
      ·
        refine ⟨18426640752004182969638809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98275417344022309171406981 18426640752004182969638809)
        ·
          refine ⟨13819980564003137227229107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18426640752004182969638809 13819980564003137227229107)
          ·
            refine ⟨20729970846004705840843661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13819980564003137227229107 20729970846004705840843661)
            ·
              refine ⟨7773739067251764690316373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20729970846004705840843661 7773739067251764690316373)
              ·
                refine ⟨91098504694356617464645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7773739067251764690316373 91098504694356617464645)
                ·
                  rfl

theorem cell23_4790170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_4790170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790170 prefixEnd_4790170 := by exact prefixLift 4790170
  have htrace : WordTrace (prefixWord ++ tailWord_4790170) baseStart_4790170 baseEnd_4790170 := by
    simpa [prefixWord, tailWord_4790170, baseEnd_4790170] using wordTrace_append hprefix tailTrace_4790170
  have hstable : (prefixWord ++ tailWord_4790170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790170).length < 2 ^ (prefixWord ++ tailWord_4790170).sum := by decide
  have hdescent : baseEnd_4790170 < baseStart_4790170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790197 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_4790197 : Nat := 118140960795 + 4790197 * 2 ^ 59
def prefixEnd_4790197 : Nat := 4983230072969 + 3 ^ 40 * 4790197 * 2
def baseEnd_4790197 : Nat := 2459673490725300065907791

theorem tailTrace_4790197 : CollatzResearch.WordTrace tailWord_4790197 prefixEnd_4790197 2459673490725300065907791 := by
  unfold tailWord_4790197
  simp only [CollatzResearch.WordTrace]
  refine ⟨174712837826941844360400845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116475225217961229573600563 174712837826941844360400845)
  ·
    refine ⟨65517314185103191635150317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174712837826941844360400845 65517314185103191635150317)
    ·
      refine ⟨24568992819413696863181369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65517314185103191635150317 24568992819413696863181369)
      ·
        refine ⟨18426744614560272647386027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24568992819413696863181369 18426744614560272647386027)
        ·
          refine ⟨27640116921840408971079041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18426744614560272647386027 27640116921840408971079041)
          ·
            refine ⟨20730087691380306728309281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27640116921840408971079041 20730087691380306728309281)
            ·
              refine ⟨15547565768535230046231961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20730087691380306728309281 15547565768535230046231961)
              ·
                refine ⟨11660674326401422534673971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15547565768535230046231961 11660674326401422534673971)
                ·
                  refine ⟨17491011489602133802010957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11660674326401422534673971 17491011489602133802010957)
                  ·
                    refine ⟨6559129308600800175754109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17491011489602133802010957 6559129308600800175754109)
                    ·
                      refine ⟨2459673490725300065907791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559129308600800175754109 2459673490725300065907791)
                      ·
                        rfl

theorem cell23_4790197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_4790197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790197 prefixEnd_4790197 := by exact prefixLift 4790197
  have htrace : WordTrace (prefixWord ++ tailWord_4790197) baseStart_4790197 baseEnd_4790197 := by
    simpa [prefixWord, tailWord_4790197, baseEnd_4790197] using wordTrace_append hprefix tailTrace_4790197
  have hstable : (prefixWord ++ tailWord_4790197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790197).length < 2 ^ (prefixWord ++ tailWord_4790197).sum := by decide
  have hdescent : baseEnd_4790197 < baseStart_4790197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790240 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3]
def baseStart_4790240 : Nat := 118140960795 + 4790240 * 2 ^ 59
def prefixEnd_4790240 : Nat := 4983230072969 + 3 ^ 40 * 4790240 * 2
def baseEnd_4790240 : Nat := 2459695570393443397670093

theorem tailTrace_4790240 : CollatzResearch.WordTrace tailWord_4790240 prefixEnd_4790240 2459695570393443397670093 := by
  unfold tailWord_4790240
  simp only [CollatzResearch.WordTrace]
  refine ⟨87357203082893031352108087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116476270777190708469477449 87357203082893031352108087)
  ·
    refine ⟨131035804624339547028162131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87357203082893031352108087 131035804624339547028162131)
    ·
      refine ⟨196553706936509320542243197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131035804624339547028162131 196553706936509320542243197)
      ·
        refine ⟨73707640101190995203341199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196553706936509320542243197 73707640101190995203341199)
        ·
          refine ⟨110561460151786492805011799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73707640101190995203341199 110561460151786492805011799)
          ·
            refine ⟨165842190227679739207517699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110561460151786492805011799 165842190227679739207517699)
            ·
              refine ⟨248763285341519608811276549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165842190227679739207517699 248763285341519608811276549)
              ·
                refine ⟨46643116001534926652114353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248763285341519608811276549 46643116001534926652114353)
                ·
                  refine ⟨34982337001151194989085765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46643116001534926652114353 34982337001151194989085765)
                  ·
                    refine ⟨6559188187715849060453581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34982337001151194989085765 6559188187715849060453581)
                    ·
                      refine ⟨2459695570393443397670093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559188187715849060453581 2459695570393443397670093)
                      ·
                        rfl

theorem cell23_4790240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_4790240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790240 prefixEnd_4790240 := by exact prefixLift 4790240
  have htrace : WordTrace (prefixWord ++ tailWord_4790240) baseStart_4790240 baseEnd_4790240 := by
    simpa [prefixWord, tailWord_4790240, baseEnd_4790240] using wordTrace_append hprefix tailTrace_4790240
  have hstable : (prefixWord ++ tailWord_4790240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790240).length < 2 ^ (prefixWord ++ tailWord_4790240).sum := by decide
  have hdescent : baseEnd_4790240 < baseStart_4790240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790257 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_4790257 : Nat := 118140960795 + 4790257 * 2 ^ 59
def prefixEnd_4790257 : Nat := 4983230072969 + 3 ^ 40 * 4790257 * 2
def baseEnd_4790257 : Nat := 2459704299564569831157515

theorem tailTrace_4790257 : CollatzResearch.WordTrace tailWord_4790257 prefixEnd_4790257 2459704299564569831157515 := by
  unfold tailWord_4790257
  simp only [CollatzResearch.WordTrace]
  refine ⟨174715026206724474607585025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116476684137816316405056683 174715026206724474607585025)
  ·
    refine ⟨131036269655043355955688769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174715026206724474607585025 131036269655043355955688769)
    ·
      refine ⟨98277202241282516966766577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131036269655043355955688769 98277202241282516966766577)
      ·
        refine ⟨73707901680961887725074933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98277202241282516966766577 73707901680961887725074933)
        ·
          refine ⟨6910115782590176974225775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73707901680961887725074933 6910115782590176974225775)
          ·
            refine ⟨10365173673885265461338663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6910115782590176974225775 10365173673885265461338663)
            ·
              refine ⟨15547760510827898192007995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10365173673885265461338663 15547760510827898192007995)
              ·
                refine ⟨23321640766241847288011993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15547760510827898192007995 23321640766241847288011993)
                ·
                  refine ⟨17491230574681385466008995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23321640766241847288011993 17491230574681385466008995)
                  ·
                    refine ⟨26236845862022078199013493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17491230574681385466008995 26236845862022078199013493)
                    ·
                      refine ⟨2459704299564569831157515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26236845862022078199013493 2459704299564569831157515)
                      ·
                        rfl

theorem cell23_4790257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_4790257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790257 prefixEnd_4790257 := by exact prefixLift 4790257
  have htrace : WordTrace (prefixWord ++ tailWord_4790257) baseStart_4790257 baseEnd_4790257 := by
    simpa [prefixWord, tailWord_4790257, baseEnd_4790257] using wordTrace_append hprefix tailTrace_4790257
  have hstable : (prefixWord ++ tailWord_4790257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790257).length < 2 ^ (prefixWord ++ tailWord_4790257).sum := by decide
  have hdescent : baseEnd_4790257 < baseStart_4790257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790277 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 7]
def baseStart_4790277 : Nat := 118140960795 + 4790277 * 2 ^ 59
def prefixEnd_4790277 : Nat := 4983230072969 + 3 ^ 40 * 4790277 * 2
def baseEnd_4790277 : Nat := 273301618797517750323047

theorem tailTrace_4790277 : CollatzResearch.WordTrace tailWord_4790277 prefixEnd_4790277 273301618797517750323047 := by
  unfold tailWord_4790277
  simp only [CollatzResearch.WordTrace]
  refine ⟨174715755666652018023313085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116477170444434678682208723 174715755666652018023313085)
  ·
    refine ⟨65518408374994506758742407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174715755666652018023313085 65518408374994506758742407)
    ·
      refine ⟨98277612562491760138113611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65518408374994506758742407 98277612562491760138113611)
      ·
        refine ⟨147416418843737640207170417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98277612562491760138113611 147416418843737640207170417)
        ·
          refine ⟨110562314132803230155377813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147416418843737640207170417 110562314132803230155377813)
          ·
            refine ⟨5182608474975151413533335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110562314132803230155377813 5182608474975151413533335)
            ·
              refine ⟨7773912712462727120300003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182608474975151413533335 7773912712462727120300003)
              ·
                refine ⟨11660869068694090680450005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773912712462727120300003 11660869068694090680450005)
                ·
                  refine ⟨273301618797517750323047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11660869068694090680450005 273301618797517750323047)
                  ·
                    rfl

theorem cell23_4790277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_4790277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790277 prefixEnd_4790277 := by exact prefixLift 4790277
  have htrace : WordTrace (prefixWord ++ tailWord_4790277) baseStart_4790277 baseEnd_4790277 := by
    simpa [prefixWord, tailWord_4790277, baseEnd_4790277] using wordTrace_append hprefix tailTrace_4790277
  have hstable : (prefixWord ++ tailWord_4790277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790277).length < 2 ^ (prefixWord ++ tailWord_4790277).sum := by decide
  have hdescent : baseEnd_4790277 < baseStart_4790277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790292 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_4790292 : Nat := 118140960795 + 4790292 * 2 ^ 59
def prefixEnd_4790292 : Nat := 4983230072969 + 3 ^ 40 * 4790292 * 2
def baseEnd_4790292 : Nat := 2459722271387477194219855

theorem tailTrace_4790292 : CollatzResearch.WordTrace tailWord_4790292 prefixEnd_4790292 2459722271387477194219855 := by
  unfold tailWord_4790292
  simp only [CollatzResearch.WordTrace]
  refine ⟨87358151380798837792554565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116477535174398450390072753 87358151380798837792554565)
  ·
    refine ⟨16379653383899782086103981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87358151380798837792554565 16379653383899782086103981)
    ·
      refine ⟨6142370018962418282288993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16379653383899782086103981 6142370018962418282288993)
      ·
        refine ⟨4606777514221813711716745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6142370018962418282288993 4606777514221813711716745)
        ·
          refine ⟨3455083135666360283787559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4606777514221813711716745 3455083135666360283787559)
          ·
            refine ⟨5182624703499540425681339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455083135666360283787559 5182624703499540425681339)
            ·
              refine ⟨7773937055249310638522009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182624703499540425681339 7773937055249310638522009)
              ·
                refine ⟨5830452791436982978891507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7773937055249310638522009 5830452791436982978891507)
                ·
                  refine ⟨8745679187155474468337261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830452791436982978891507 8745679187155474468337261)
                  ·
                    refine ⟨3279629695183302925626473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8745679187155474468337261 3279629695183302925626473)
                    ·
                      refine ⟨2459722271387477194219855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279629695183302925626473 2459722271387477194219855)
                      ·
                        rfl

theorem cell23_4790292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_4790292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790292 prefixEnd_4790292 := by exact prefixLift 4790292
  have htrace : WordTrace (prefixWord ++ tailWord_4790292) baseStart_4790292 baseEnd_4790292 := by
    simpa [prefixWord, tailWord_4790292, baseEnd_4790292] using wordTrace_append hprefix tailTrace_4790292
  have hstable : (prefixWord ++ tailWord_4790292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790292).length < 2 ^ (prefixWord ++ tailWord_4790292).sum := by decide
  have hdescent : baseEnd_4790292 < baseStart_4790292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790307 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 2, 5]
def baseStart_4790307 : Nat := 118140960795 + 4790307 * 2 ^ 59
def prefixEnd_4790307 : Nat := 4983230072969 + 3 ^ 40 * 4790307 * 2
def baseEnd_4790307 : Nat := 819909991199098211844095

theorem tailTrace_4790307 : CollatzResearch.WordTrace tailWord_4790307 prefixEnd_4790307 819909991199098211844095 := by
  unfold tailWord_4790307
  simp only [CollatzResearch.WordTrace]
  refine ⟨174716849856543333146905175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116477899904362222097936783 174716849856543333146905175)
  ·
    refine ⟨262075274784814999720357763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174716849856543333146905175 262075274784814999720357763)
    ·
      refine ⟨393112912177222499580536645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262075274784814999720357763 393112912177222499580536645)
      ·
        refine ⟨73708671033229218671350621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 393112912177222499580536645 73708671033229218671350621)
        ·
          refine ⟨27640751637460957001756483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73708671033229218671350621 27640751637460957001756483)
          ·
            refine ⟨41461127456191435502634725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27640751637460957001756483 41461127456191435502634725)
            ·
              refine ⟨7773961398035894156744011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41461127456191435502634725 7773961398035894156744011)
              ·
                refine ⟨11660942097053841235116017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773961398035894156744011 11660942097053841235116017)
                ·
                  refine ⟨8745706572790380926337013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11660942097053841235116017 8745706572790380926337013)
                  ·
                    refine ⟨819909991199098211844095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8745706572790380926337013 819909991199098211844095)
                    ·
                      rfl

theorem cell23_4790307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 5].length) (baseStart_4790307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790307 prefixEnd_4790307 := by exact prefixLift 4790307
  have htrace : WordTrace (prefixWord ++ tailWord_4790307) baseStart_4790307 baseEnd_4790307 := by
    simpa [prefixWord, tailWord_4790307, baseEnd_4790307] using wordTrace_append hprefix tailTrace_4790307
  have hstable : (prefixWord ++ tailWord_4790307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790307).length < 2 ^ (prefixWord ++ tailWord_4790307).sum := by decide
  have hdescent : baseEnd_4790307 < baseStart_4790307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790327 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_4790327 : Nat := 118140960795 + 4790327 * 2 ^ 59
def prefixEnd_4790327 : Nat := 4983230072969 + 3 ^ 40 * 4790327 * 2
def baseEnd_4790327 : Nat := 2459740243210384557282193

theorem tailTrace_4790327 : CollatzResearch.WordTrace tailWord_4790327 prefixEnd_4790327 2459740243210384557282193 := by
  unfold tailWord_4790327
  simp only [CollatzResearch.WordTrace]
  refine ⟨174717579316470876562633235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116478386210980584375088823 174717579316470876562633235)
  ·
    refine ⟨262076368974706314843949853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174717579316470876562633235 262076368974706314843949853)
    ·
      refine ⟨98278638365514868066481195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262076368974706314843949853 98278638365514868066481195)
      ·
        refine ⟨147417957548272302099721793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98278638365514868066481195 147417957548272302099721793)
        ·
          refine ⟨110563468161204226574791345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147417957548272302099721793 110563468161204226574791345)
          ·
            refine ⟨82922601120903169931093509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110563468161204226574791345 82922601120903169931093509)
            ·
              refine ⟨15547987710169344362080033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82922601120903169931093509 15547987710169344362080033)
              ·
                refine ⟨11660990782627008271560025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15547987710169344362080033 11660990782627008271560025)
                ·
                  refine ⟨8745743086970256203670019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11660990782627008271560025 8745743086970256203670019)
                  ·
                    refine ⟨13118614630455384305505029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8745743086970256203670019 13118614630455384305505029)
                    ·
                      refine ⟨2459740243210384557282193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13118614630455384305505029 2459740243210384557282193)
                      ·
                        rfl

theorem cell23_4790327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_4790327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790327 prefixEnd_4790327 := by exact prefixLift 4790327
  have htrace : WordTrace (prefixWord ++ tailWord_4790327) baseStart_4790327 baseEnd_4790327 := by
    simpa [prefixWord, tailWord_4790327, baseEnd_4790327] using wordTrace_append hprefix tailTrace_4790327
  have hstable : (prefixWord ++ tailWord_4790327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790327).length < 2 ^ (prefixWord ++ tailWord_4790327).sum := by decide
  have hdescent : baseEnd_4790327 < baseStart_4790327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790328 : List Nat := [2, 1, 2, 1, 7, 1, 2, 2, 5]
def baseStart_4790328 : Nat := 118140960795 + 4790328 * 2 ^ 59
def prefixEnd_4790328 : Nat := 4983230072969 + 3 ^ 40 * 4790328 * 2
def baseEnd_4790328 : Nat := 273304528521226561485521

theorem tailTrace_4790328 : CollatzResearch.WordTrace tailWord_4790328 prefixEnd_4790328 273304528521226561485521 := by
  unfold tailWord_4790328
  simp only [CollatzResearch.WordTrace]
  refine ⟨87358807894733626866709819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116478410526311502488946425 87358807894733626866709819)
  ·
    refine ⟨131038211842100440300064729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87358807894733626866709819 131038211842100440300064729)
    ·
      refine ⟨98278658881575330225048547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131038211842100440300064729 98278658881575330225048547)
      ·
        refine ⟨147417988322362995337572821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98278658881575330225048547 147417988322362995337572821)
        ·
          refine ⟨3455109101305382703224363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 147417988322362995337572821 3455109101305382703224363)
          ·
            refine ⟨5182663651958074054836545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455109101305382703224363 5182663651958074054836545)
            ·
              refine ⟨3886997738968555541127409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5182663651958074054836545 3886997738968555541127409)
              ·
                refine ⟨2915248304226416655845557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3886997738968555541127409 2915248304226416655845557)
                ·
                  refine ⟨273304528521226561485521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2915248304226416655845557 273304528521226561485521)
                  ·
                    rfl

theorem cell23_4790328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 5].length) (baseStart_4790328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790328 prefixEnd_4790328 := by exact prefixLift 4790328
  have htrace : WordTrace (prefixWord ++ tailWord_4790328) baseStart_4790328 baseEnd_4790328 := by
    simpa [prefixWord, tailWord_4790328, baseEnd_4790328] using wordTrace_append hprefix tailTrace_4790328
  have hstable : (prefixWord ++ tailWord_4790328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790328).length < 2 ^ (prefixWord ++ tailWord_4790328).sum := by decide
  have hdescent : baseEnd_4790328 < baseStart_4790328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790330 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_4790330 : Nat := 118140960795 + 4790330 * 2 ^ 59
def prefixEnd_4790330 : Nat := 4983230072969 + 3 ^ 40 * 4790330 * 2
def baseEnd_4790330 : Nat := 2459741783652348045544679

theorem tailTrace_4790330 : CollatzResearch.WordTrace tailWord_4790330 prefixEnd_4790330 2459741783652348045544679 := by
  unfold tailWord_4790330
  simp only [CollatzResearch.WordTrace]
  refine ⟨43679422183865002018748111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116478459156973338716661629 43679422183865002018748111)
  ·
    refine ⟨65519133275797503028122167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43679422183865002018748111 65519133275797503028122167)
    ·
      refine ⟨98278699913696254542183251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65519133275797503028122167 98278699913696254542183251)
      ·
        refine ⟨147418049870544381813274877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98278699913696254542183251 147418049870544381813274877)
        ·
          refine ⟨55281768701454143179978079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147418049870544381813274877 55281768701454143179978079)
          ·
            refine ⟨82922653052181214769967119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55281768701454143179978079 82922653052181214769967119)
            ·
              refine ⟨124383979578271822154950679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82922653052181214769967119 124383979578271822154950679)
              ·
                refine ⟨186575969367407733232426019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124383979578271822154950679 186575969367407733232426019)
                ·
                  refine ⟨279863954051111599848639029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186575969367407733232426019 279863954051111599848639029)
                  ·
                    refine ⟨26237245692291712485809909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 279863954051111599848639029 26237245692291712485809909)
                    ·
                      refine ⟨2459741783652348045544679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26237245692291712485809909 2459741783652348045544679)
                      ·
                        rfl

theorem cell23_4790330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_4790330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790330 prefixEnd_4790330 := by exact prefixLift 4790330
  have htrace : WordTrace (prefixWord ++ tailWord_4790330) baseStart_4790330 baseEnd_4790330 := by
    simpa [prefixWord, tailWord_4790330, baseEnd_4790330] using wordTrace_append hprefix tailTrace_4790330
  have hstable : (prefixWord ++ tailWord_4790330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790330).length < 2 ^ (prefixWord ++ tailWord_4790330).sum := by decide
  have hdescent : baseEnd_4790330 < baseStart_4790330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790358 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4790358 : Nat := 118140960795 + 4790358 * 2 ^ 59
def prefixEnd_4790358 : Nat := 4983230072969 + 3 ^ 40 * 4790358 * 2
def baseEnd_4790358 : Nat := 819918720370224645331517

theorem tailTrace_4790358 : CollatzResearch.WordTrace tailWord_4790358 prefixEnd_4790358 819918720370224645331517 := by
  unfold tailWord_4790358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10919919373709910553563233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116479139986239045904674485 10919919373709910553563233)
  ·
    refine ⟨8189939530282432915172425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10919919373709910553563233 8189939530282432915172425)
    ·
      refine ⟨6142454647711824686379319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8189939530282432915172425 6142454647711824686379319)
      ·
        refine ⟨9213681971567737029568979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6142454647711824686379319 9213681971567737029568979)
        ·
          refine ⟨13820522957351605544353469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9213681971567737029568979 13820522957351605544353469)
          ·
            refine ⟨5182696109006852079132551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13820522957351605544353469 5182696109006852079132551)
            ·
              refine ⟨7774044163510278118698827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182696109006852079132551 7774044163510278118698827)
              ·
                refine ⟨11661066245265417178048241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7774044163510278118698827 11661066245265417178048241)
                ·
                  refine ⟨8745799683949062883536181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11661066245265417178048241 8745799683949062883536181)
                  ·
                    refine ⟨819918720370224645331517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8745799683949062883536181 819918720370224645331517)
                    ·
                      rfl

theorem cell23_4790358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4790358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790358 prefixEnd_4790358 := by exact prefixLift 4790358
  have htrace : WordTrace (prefixWord ++ tailWord_4790358) baseStart_4790358 baseEnd_4790358 := by
    simpa [prefixWord, tailWord_4790358, baseEnd_4790358] using wordTrace_append hprefix tailTrace_4790358
  have hstable : (prefixWord ++ tailWord_4790358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790358).length < 2 ^ (prefixWord ++ tailWord_4790358).sum := by decide
  have hdescent : baseEnd_4790358 < baseStart_4790358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790364 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_4790364 : Nat := 118140960795 + 4790364 * 2 ^ 59
def prefixEnd_4790364 : Nat := 4983230072969 + 3 ^ 40 * 4790364 * 2
def baseEnd_4790364 : Nat := 2459759241994600912519523

theorem tailTrace_4790364 : CollatzResearch.WordTrace tailWord_4790364 prefixEnd_4790364 2459759241994600912519523 := by
  unfold tailWord_4790364
  simp only [CollatzResearch.WordTrace]
  refine ⟨87359464408668415940865073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116479285878224554587820097 87359464408668415940865073)
  ·
    refine ⟨65519598306501311955648805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87359464408668415940865073 65519598306501311955648805)
    ·
      refine ⟨12284924682468995991684151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65519598306501311955648805 12284924682468995991684151)
      ·
        refine ⟨18427387023703493987526227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12284924682468995991684151 18427387023703493987526227)
        ·
          refine ⟨27641080535555240981289341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18427387023703493987526227 27641080535555240981289341)
          ·
            refine ⟨10365405200833215367983503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27641080535555240981289341 10365405200833215367983503)
            ·
              refine ⟨15548107801249823051975255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10365405200833215367983503 15548107801249823051975255)
              ·
                refine ⟨23322161701874734577962883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15548107801249823051975255 23322161701874734577962883)
                ·
                  refine ⟨34983242552812101866944325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23322161701874734577962883 34983242552812101866944325)
                  ·
                    refine ⟨6559357978652269100052061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34983242552812101866944325 6559357978652269100052061)
                    ·
                      refine ⟨2459759241994600912519523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559357978652269100052061 2459759241994600912519523)
                      ·
                        rfl

theorem cell23_4790364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_4790364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790364 prefixEnd_4790364 := by exact prefixLift 4790364
  have htrace : WordTrace (prefixWord ++ tailWord_4790364) baseStart_4790364 baseEnd_4790364 := by
    simpa [prefixWord, tailWord_4790364, baseEnd_4790364] using wordTrace_append hprefix tailTrace_4790364
  have hstable : (prefixWord ++ tailWord_4790364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790364).length < 2 ^ (prefixWord ++ tailWord_4790364).sum := by decide
  have hdescent : baseEnd_4790364 < baseStart_4790364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790384 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 6]
def baseStart_4790384 : Nat := 118140960795 + 4790384 * 2 ^ 59
def prefixEnd_4790384 : Nat := 4983230072969 + 3 ^ 40 * 4790384 * 2
def baseEnd_4790384 : Nat := 273307723511965648252159

theorem tailTrace_4790384 : CollatzResearch.WordTrace tailWord_4790384 prefixEnd_4790384 273307723511965648252159 := by
  unfold tailWord_4790384
  simp only [CollatzResearch.WordTrace]
  refine ⟨87359829138632187648729103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116479772184842916864972137 87359829138632187648729103)
  ·
    refine ⟨131039743707948281473093655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87359829138632187648729103 131039743707948281473093655)
    ·
      refine ⟨196559615561922422209640483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131039743707948281473093655 196559615561922422209640483)
      ·
        refine ⟨294839423342883633314460725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196559615561922422209640483 294839423342883633314460725)
        ·
          refine ⟨27641195938395340623230693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 294839423342883633314460725 27641195938395340623230693)
          ·
            refine ⟨5182724238449126366855755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27641195938395340623230693 5182724238449126366855755)
            ·
              refine ⟨7774086357673689550283633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182724238449126366855755 7774086357673689550283633)
              ·
                refine ⟨5830564768255267162712725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7774086357673689550283633 5830564768255267162712725)
                ·
                  refine ⟨273307723511965648252159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5830564768255267162712725 273307723511965648252159)
                  ·
                    rfl

theorem cell23_4790384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 6].length) (baseStart_4790384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790384 prefixEnd_4790384 := by exact prefixLift 4790384
  have htrace : WordTrace (prefixWord ++ tailWord_4790384) baseStart_4790384 baseEnd_4790384 := by
    simpa [prefixWord, tailWord_4790384, baseEnd_4790384] using wordTrace_append hprefix tailTrace_4790384
  have hstable : (prefixWord ++ tailWord_4790384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790384).length < 2 ^ (prefixWord ++ tailWord_4790384).sum := by decide
  have hdescent : baseEnd_4790384 < baseStart_4790384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790401 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 6]
def baseStart_4790401 : Nat := 118140960795 + 4790401 * 2 ^ 59
def prefixEnd_4790401 : Nat := 4983230072969 + 3 ^ 40 * 4790401 * 2
def baseEnd_4790401 : Nat := 273308693419868585306317

theorem tailTrace_4790401 : CollatzResearch.WordTrace tailWord_4790401 prefixEnd_4790401 273308693419868585306317 := by
  unfold tailWord_4790401
  simp only [CollatzResearch.WordTrace]
  refine ⟨174720278318202787200827057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116480185545468524800551371 174720278318202787200827057)
  ·
    refine ⟨131040208738652090400620293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174720278318202787200827057 131040208738652090400620293)
    ·
      refine ⟨24570039138497266950116305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131040208738652090400620293 24570039138497266950116305)
      ·
        refine ⟨18427529353872950212587229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24570039138497266950116305 18427529353872950212587229)
        ·
          refine ⟨6910323507702356329720211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18427529353872950212587229 6910323507702356329720211)
          ·
            refine ⟨10365485261553534494580317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6910323507702356329720211 10365485261553534494580317)
            ·
              refine ⟨3887056973082575435467619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10365485261553534494580317 3887056973082575435467619)
              ·
                refine ⟨5830585459623863153201429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887056973082575435467619 5830585459623863153201429)
                ·
                  refine ⟨273308693419868585306317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5830585459623863153201429 273308693419868585306317)
                  ·
                    rfl

theorem cell23_4790401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 6].length) (baseStart_4790401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790401 prefixEnd_4790401 := by exact prefixLift 4790401
  have htrace : WordTrace (prefixWord ++ tailWord_4790401) baseStart_4790401 baseEnd_4790401 := by
    simpa [prefixWord, tailWord_4790401, baseEnd_4790401] using wordTrace_append hprefix tailTrace_4790401
  have hstable : (prefixWord ++ tailWord_4790401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790401).length < 2 ^ (prefixWord ++ tailWord_4790401).sum := by decide
  have hdescent : baseEnd_4790401 < baseStart_4790401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790404 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_4790404 : Nat := 118140960795 + 4790404 * 2 ^ 59
def prefixEnd_4790404 : Nat := 4983230072969 + 3 ^ 40 * 4790404 * 2
def baseEnd_4790404 : Nat := 2459779781220780756019339

theorem tailTrace_4790404 : CollatzResearch.WordTrace tailWord_4790404 prefixEnd_4790404 2459779781220780756019339 := by
  unfold tailWord_4790404
  simp only [CollatzResearch.WordTrace]
  refine ⟨87360193868595959356593133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116480258491461279142124177 87360193868595959356593133)
  ·
    refine ⟨32760072700723484758722425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87360193868595959356593133 32760072700723484758722425)
    ·
      refine ⟨24570054525542613569041819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32760072700723484758722425 24570054525542613569041819)
      ·
        refine ⟨36855081788313920353562729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24570054525542613569041819 36855081788313920353562729)
        ·
          refine ⟨27641311341235440265172047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36855081788313920353562729 27641311341235440265172047)
          ·
            refine ⟨41461967011853160397758071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27641311341235440265172047 41461967011853160397758071)
            ·
              refine ⟨62192950517779740596637107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41461967011853160397758071 62192950517779740596637107)
              ·
                refine ⟨93289425776669610894955661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62192950517779740596637107 93289425776669610894955661)
                ·
                  refine ⟨34983534666251104085608373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93289425776669610894955661 34983534666251104085608373)
                  ·
                    refine ⟨3279706374961041008025785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34983534666251104085608373 3279706374961041008025785)
                    ·
                      refine ⟨2459779781220780756019339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279706374961041008025785 2459779781220780756019339)
                      ·
                        rfl

theorem cell23_4790404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_4790404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790404 prefixEnd_4790404 := by exact prefixLift 4790404
  have htrace : WordTrace (prefixWord ++ tailWord_4790404) baseStart_4790404 baseEnd_4790404 := by
    simpa [prefixWord, tailWord_4790404, baseEnd_4790404] using wordTrace_append hprefix tailTrace_4790404
  have hstable : (prefixWord ++ tailWord_4790404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790404).length < 2 ^ (prefixWord ++ tailWord_4790404).sum := by decide
  have hdescent : baseEnd_4790404 < baseStart_4790404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790427 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 6, 4]
def baseStart_4790427 : Nat := 118140960795 + 4790427 * 2 ^ 59
def prefixEnd_4790427 : Nat := 4983230072969 + 3 ^ 40 * 4790427 * 2
def baseEnd_4790427 : Nat := 819930530425278055343911

theorem tailTrace_4790427 : CollatzResearch.WordTrace tailWord_4790427 prefixEnd_4790427 819930530425278055343911 := by
  unfold tailWord_4790427
  simp only [CollatzResearch.WordTrace]
  refine ⟨174721226616108593641273535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116480817744072395760849023 174721226616108593641273535)
  ·
    refine ⟨262081839924162890461910303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174721226616108593641273535 262081839924162890461910303)
    ·
      refine ⟨393122759886244335692865455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262081839924162890461910303 393122759886244335692865455)
      ·
        refine ⟨589684139829366503539298183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393122759886244335692865455 589684139829366503539298183)
        ·
          refine ⟨884526209744049755308947275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589684139829366503539298183 884526209744049755308947275)
          ·
            refine ⟨1326789314616074632963420913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884526209744049755308947275 1326789314616074632963420913)
            ·
              refine ⟨995091985962055974722565685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326789314616074632963420913 995091985962055974722565685)
              ·
                refine ⟨93289873683942747630240533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 995091985962055974722565685 93289873683942747630240533)
                ·
                  refine ⟨4372962828934816295167525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93289873683942747630240533 4372962828934816295167525)
                  ·
                    refine ⟨819930530425278055343911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4372962828934816295167525 819930530425278055343911)
                    ·
                      rfl

theorem cell23_4790427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 4].length) (baseStart_4790427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790427 prefixEnd_4790427 := by exact prefixLift 4790427
  have htrace : WordTrace (prefixWord ++ tailWord_4790427) baseStart_4790427 baseEnd_4790427 := by
    simpa [prefixWord, tailWord_4790427, baseEnd_4790427] using wordTrace_append hprefix tailTrace_4790427
  have hstable : (prefixWord ++ tailWord_4790427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790427).length < 2 ^ (prefixWord ++ tailWord_4790427).sum := by decide
  have hdescent : baseEnd_4790427 < baseStart_4790427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790452 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 6]
def baseStart_4790452 : Nat := 118140960795 + 4790452 * 2 ^ 59
def prefixEnd_4790452 : Nat := 4983230072969 + 3 ^ 40 * 4790452 * 2
def baseEnd_4790452 : Nat := 273311603143577396468791

theorem tailTrace_4790452 : CollatzResearch.WordTrace tailWord_4790452 prefixEnd_4790452 273311603143577396468791 := by
  unfold tailWord_4790452
  simp only [CollatzResearch.WordTrace]
  refine ⟨87361069220509011455466805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116481425627345348607289073 87361069220509011455466805)
  ·
    refine ⟨8190100239422719823950013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87361069220509011455466805 8190100239422719823950013)
    ·
      refine ⟨3071287589783519933981255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8190100239422719823950013 3071287589783519933981255)
      ·
        refine ⟨4606931384675279900971883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071287589783519933981255 4606931384675279900971883)
        ·
          refine ⟨6910397077012919851457825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606931384675279900971883 6910397077012919851457825)
          ·
            refine ⟨5182797807759689888593369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6910397077012919851457825 5182797807759689888593369)
            ·
              refine ⟨3887098355819767416445027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5182797807759689888593369 3887098355819767416445027)
              ·
                refine ⟨5830647533729651124667541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887098355819767416445027 5830647533729651124667541)
                ·
                  refine ⟨273311603143577396468791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5830647533729651124667541 273311603143577396468791)
                  ·
                    rfl

theorem cell23_4790452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_4790452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790452 prefixEnd_4790452 := by exact prefixLift 4790452
  have htrace : WordTrace (prefixWord ++ tailWord_4790452) baseStart_4790452 baseEnd_4790452 := by
    simpa [prefixWord, tailWord_4790452, baseEnd_4790452] using wordTrace_append hprefix tailTrace_4790452
  have hstable : (prefixWord ++ tailWord_4790452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790452).length < 2 ^ (prefixWord ++ tailWord_4790452).sum := by decide
  have hdescent : baseEnd_4790452 < baseStart_4790452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790457 : List Nat := [1, 2, 1, 4, 1, 2, 4, 8]
def baseStart_4790457 : Nat := 118140960795 + 4790457 * 2 ^ 59
def prefixEnd_4790457 : Nat := 4983230072969 + 3 ^ 40 * 4790457 * 2
def baseEnd_4790457 : Nat := 91103962803535890690985

theorem tailTrace_4790457 : CollatzResearch.WordTrace tailWord_4790457 prefixEnd_4790457 91103962803535890690985 := by
  unfold tailWord_4790457
  simp only [CollatzResearch.WordTrace]
  refine ⟨174722320805999908764865625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116481547203999939176577083 174722320805999908764865625)
  ·
    refine ⟨131041740604499931573649219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174722320805999908764865625 131041740604499931573649219)
    ·
      refine ⟨196562610906749897360473829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131041740604499931573649219 196562610906749897360473829)
      ·
        refine ⟨36855489545015605755088843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196562610906749897360473829 36855489545015605755088843)
        ·
          refine ⟨55283234317523408632633265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36855489545015605755088843 55283234317523408632633265)
          ·
            refine ⟨41462425738142556474474949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55283234317523408632633265 41462425738142556474474949)
            ·
              refine ⟨7774204825901729338964053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41462425738142556474474949 7774204825901729338964053)
              ·
                refine ⟨91103962803535890690985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7774204825901729338964053 91103962803535890690985)
                ·
                  rfl

theorem cell23_4790457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 8].length) (baseStart_4790457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790457 prefixEnd_4790457 := by exact prefixLift 4790457
  have htrace : WordTrace (prefixWord ++ tailWord_4790457) baseStart_4790457 baseEnd_4790457 := by
    simpa [prefixWord, tailWord_4790457, baseEnd_4790457] using wordTrace_append hprefix tailTrace_4790457
  have hstable : (prefixWord ++ tailWord_4790457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790457).length < 2 ^ (prefixWord ++ tailWord_4790457).sum := by decide
  have hdescent : baseEnd_4790457 < baseStart_4790457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790465 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4790465 : Nat := 118140960795 + 4790465 * 2 ^ 59
def prefixEnd_4790465 : Nat := 4983230072969 + 3 ^ 40 * 4790465 * 2
def baseEnd_4790465 : Nat := 819937034513568339118853

theorem tailTrace_4790465 : CollatzResearch.WordTrace tailWord_4790465 prefixEnd_4790465 819937034513568339118853 := by
  unfold tailWord_4790465
  simp only [CollatzResearch.WordTrace]
  refine ⟨174722612589970926131156849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116481741726647284087437899 174722612589970926131156849)
  ·
    refine ⟨131041959442478194598367637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174722612589970926131156849 131041959442478194598367637)
    ·
      refine ⟨6142591848866165371798483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131041959442478194598367637 6142591848866165371798483)
      ·
        refine ⟨9213887773299248057697725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6142591848866165371798483 9213887773299248057697725)
        ·
          refine ⟨3455207914987218021636647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9213887773299248057697725 3455207914987218021636647)
          ·
            refine ⟨5182811872480827032454971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455207914987218021636647 5182811872480827032454971)
            ·
              refine ⟨7774217808721240548682457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182811872480827032454971 7774217808721240548682457)
              ·
                refine ⟨5830663356540930411511843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7774217808721240548682457 5830663356540930411511843)
                ·
                  refine ⟨8745995034811395617267765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830663356540930411511843 8745995034811395617267765)
                  ·
                    refine ⟨819937034513568339118853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8745995034811395617267765 819937034513568339118853)
                    ·
                      rfl

theorem cell23_4790465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4790465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790465 prefixEnd_4790465 := by exact prefixLift 4790465
  have htrace : WordTrace (prefixWord ++ tailWord_4790465) baseStart_4790465 baseEnd_4790465 := by
    simpa [prefixWord, tailWord_4790465, baseEnd_4790465] using wordTrace_append hprefix tailTrace_4790465
  have hstable : (prefixWord ++ tailWord_4790465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790465).length < 2 ^ (prefixWord ++ tailWord_4790465).sum := by decide
  have hdescent : baseEnd_4790465 < baseStart_4790465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790468 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_4790468 : Nat := 118140960795 + 4790468 * 2 ^ 59
def prefixEnd_4790468 : Nat := 4983230072969 + 3 ^ 40 * 4790468 * 2
def baseEnd_4790468 : Nat := 2459812643982668505619045

theorem tailTrace_4790468 : CollatzResearch.WordTrace tailWord_4790468 prefixEnd_4790468 2459812643982668505619045 := by
  unfold tailWord_4790468
  simp only [CollatzResearch.WordTrace]
  refine ⟨87361361004480028821758029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116481814672640038429010705 87361361004480028821758029)
  ·
    refine ⟨32760510376680010808159261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87361361004480028821758029 32760510376680010808159261)
    ·
      refine ⟨12285191391255004053059723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32760510376680010808159261 12285191391255004053059723)
      ·
        refine ⟨18427787086882506079589585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12285191391255004053059723 18427787086882506079589585)
        ·
          refine ⟨13820840315161879559692189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18427787086882506079589585 13820840315161879559692189)
          ·
            refine ⟨5182815118185704834884571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13820840315161879559692189 5182815118185704834884571)
            ·
              refine ⟨7774222677278557252326857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182815118185704834884571 7774222677278557252326857)
              ·
                refine ⟨5830667007958917939245143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7774222677278557252326857 5830667007958917939245143)
                ·
                  refine ⟨8746000511938376908867715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830667007958917939245143 8746000511938376908867715)
                  ·
                    refine ⟨13119000767907565363301573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8746000511938376908867715 13119000767907565363301573)
                    ·
                      refine ⟨2459812643982668505619045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13119000767907565363301573 2459812643982668505619045)
                      ·
                        rfl

theorem cell23_4790468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_4790468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790468 prefixEnd_4790468 := by exact prefixLift 4790468
  have htrace : WordTrace (prefixWord ++ tailWord_4790468) baseStart_4790468 baseEnd_4790468 := by
    simpa [prefixWord, tailWord_4790468, baseEnd_4790468] using wordTrace_append hprefix tailTrace_4790468
  have hstable : (prefixWord ++ tailWord_4790468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790468).length < 2 ^ (prefixWord ++ tailWord_4790468).sum := by decide
  have hdescent : baseEnd_4790468 < baseStart_4790468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790488 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 1, 2, 3]
def baseStart_4790488 : Nat := 118140960795 + 4790488 * 2 ^ 59
def prefixEnd_4790488 : Nat := 4983230072969 + 3 ^ 40 * 4790488 * 2
def baseEnd_4790488 : Nat := 2459822913595758427368953

theorem tailTrace_4790488 : CollatzResearch.WordTrace tailWord_4790488 prefixEnd_4790488 2459822913595758427368953 := by
  unfold tailWord_4790488
  simp only [CollatzResearch.WordTrace]
  refine ⟨87361725734443800529622059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116482300979258400706162745 87361725734443800529622059)
  ·
    refine ⟨131042588601665700794433089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87361725734443800529622059 131042588601665700794433089)
    ·
      refine ⟨98281941451249275595824817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131042588601665700794433089 98281941451249275595824817)
      ·
        refine ⟨73711456088436956696868613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98281941451249275595824817 73711456088436956696868613)
        ·
          refine ⟨13820898016581929380662865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73711456088436956696868613 13820898016581929380662865)
          ·
            refine ⟨10365673512436447035497149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13820898016581929380662865 10365673512436447035497149)
            ·
              refine ⟨3887127567163667638311431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10365673512436447035497149 3887127567163667638311431)
              ·
                refine ⟨5830691350745501457467147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887127567163667638311431 5830691350745501457467147)
                ·
                  refine ⟨8746037026118252186200721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830691350745501457467147 8746037026118252186200721)
                  ·
                    refine ⟨6559527769588689139650541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8746037026118252186200721 6559527769588689139650541)
                    ·
                      refine ⟨2459822913595758427368953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559527769588689139650541 2459822913595758427368953)
                      ·
                        rfl

theorem cell23_4790488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_4790488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790488 prefixEnd_4790488 := by exact prefixLift 4790488
  have htrace : WordTrace (prefixWord ++ tailWord_4790488) baseStart_4790488 baseEnd_4790488 := by
    simpa [prefixWord, tailWord_4790488, baseEnd_4790488] using wordTrace_append hprefix tailTrace_4790488
  have hstable : (prefixWord ++ tailWord_4790488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790488).length < 2 ^ (prefixWord ++ tailWord_4790488).sum := by decide
  have hdescent : baseEnd_4790488 < baseStart_4790488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790507 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4]
def baseStart_4790507 : Nat := 118140960795 + 4790507 * 2 ^ 59
def prefixEnd_4790507 : Nat := 4983230072969 + 3 ^ 40 * 4790507 * 2
def baseEnd_4790507 : Nat := 2459832669728193853031365

theorem tailTrace_4790507 : CollatzResearch.WordTrace tailWord_4790507 prefixEnd_4790507 2459832669728193853031365 := by
  unfold tailWord_4790507
  simp only [CollatzResearch.WordTrace]
  refine ⟨174724144455818767304185775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116482762970545844869457183 174724144455818767304185775)
  ·
    refine ⟨262086216683728150956278663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174724144455818767304185775 262086216683728150956278663)
    ·
      refine ⟨393129325025592226434417995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262086216683728150956278663 393129325025592226434417995)
      ·
        refine ⟨589693987538388339651626993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393129325025592226434417995 589693987538388339651626993)
        ·
          refine ⟨442270490653791254738720245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589693987538388339651626993 442270490653791254738720245)
          ·
            refine ⟨41462858498792930131755023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 442270490653791254738720245 41462858498792930131755023)
            ·
              refine ⟨62194287748189395197632535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41462858498792930131755023 62194287748189395197632535)
              ·
                refine ⟨93291431622284092796448803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62194287748189395197632535 93291431622284092796448803)
                ·
                  refine ⟨139937147433426139194673205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93291431622284092796448803 139937147433426139194673205)
                  ·
                    refine ⟨13119107571883700549500613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 139937147433426139194673205 13119107571883700549500613)
                    ·
                      refine ⟨2459832669728193853031365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13119107571883700549500613 2459832669728193853031365)
                      ·
                        rfl

theorem cell23_4790507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_4790507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790507 prefixEnd_4790507 := by exact prefixLift 4790507
  have htrace : WordTrace (prefixWord ++ tailWord_4790507) baseStart_4790507 baseEnd_4790507 := by
    simpa [prefixWord, tailWord_4790507, baseEnd_4790507] using wordTrace_append hprefix tailTrace_4790507
  have hstable : (prefixWord ++ tailWord_4790507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790507).length < 2 ^ (prefixWord ++ tailWord_4790507).sum := by decide
  have hdescent : baseEnd_4790507 < baseStart_4790507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790511 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 3, 3, 2]
def baseStart_4790511 : Nat := 118140960795 + 4790511 * 2 ^ 59
def prefixEnd_4790511 : Nat := 4983230072969 + 3 ^ 40 * 4790511 * 2
def baseEnd_4790511 : Nat := 2459834723650811837381347

theorem tailTrace_4790511 : CollatzResearch.WordTrace tailWord_4790511 prefixEnd_4790511 2459834723650811837381347 := by
  unfold tailWord_4790511
  simp only [CollatzResearch.WordTrace]
  refine ⟨174724290347804275987331387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116482860231869517324887591 174724290347804275987331387)
  ·
    refine ⟨262086435521706413980997081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174724290347804275987331387 262086435521706413980997081)
    ·
      refine ⟨196564826641279810485747811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262086435521706413980997081 196564826641279810485747811)
      ·
        refine ⟨294847239961919715728621717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196564826641279810485747811 294847239961919715728621717)
        ·
          refine ⟨13820964373214986674779143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 294847239961919715728621717 13820964373214986674779143)
          ·
            refine ⟨20731446559822480012168715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13820964373214986674779143 20731446559822480012168715)
            ·
              refine ⟨31097169839733720018253073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20731446559822480012168715 31097169839733720018253073)
              ·
                refine ⟨23322877379800290013689805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31097169839733720018253073 23322877379800290013689805)
                ·
                  refine ⟨8746079017425108755133677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23322877379800290013689805 8746079017425108755133677)
                  ·
                    refine ⟨3279779631534415783175129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8746079017425108755133677 3279779631534415783175129)
                    ·
                      refine ⟨2459834723650811837381347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279779631534415783175129 2459834723650811837381347)
                      ·
                        rfl

theorem cell23_4790511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3, 2].length) (baseStart_4790511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790511 prefixEnd_4790511 := by exact prefixLift 4790511
  have htrace : WordTrace (prefixWord ++ tailWord_4790511) baseStart_4790511 baseEnd_4790511 := by
    simpa [prefixWord, tailWord_4790511, baseEnd_4790511] using wordTrace_append hprefix tailTrace_4790511
  have hstable : (prefixWord ++ tailWord_4790511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790511).length < 2 ^ (prefixWord ++ tailWord_4790511).sum := by decide
  have hdescent : baseEnd_4790511 < baseStart_4790511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790518 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4790518 : Nat := 118140960795 + 4790518 * 2 ^ 59
def prefixEnd_4790518 : Nat := 4983230072969 + 3 ^ 40 * 4790518 * 2
def baseEnd_4790518 : Nat := 2459838318015393309993815

theorem tailTrace_4790518 : CollatzResearch.WordTrace tailWord_4790518 prefixEnd_4790518 2459838318015393309993815 := by
  unfold tailWord_4790518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10920284103673682261427263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116483030439185944121890805 10920284103673682261427263)
  ·
    refine ⟨16380426155510523392140895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10920284103673682261427263 16380426155510523392140895)
    ·
      refine ⟨24570639233265785088211343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16380426155510523392140895 24570639233265785088211343)
      ·
        refine ⟨36855958849898677632317015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24570639233265785088211343 36855958849898677632317015)
        ·
          refine ⟨55283938274848016448475523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36855958849898677632317015 55283938274848016448475523)
          ·
            refine ⟨82925907412272024672713285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55283938274848016448475523 82925907412272024672713285)
            ·
              refine ⟨15548607639801004626133741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82925907412272024672713285 15548607639801004626133741)
              ·
                refine ⟨5830727864925376734800153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15548607639801004626133741 5830727864925376734800153)
                ·
                  refine ⟨4373045898694032551100115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5830727864925376734800153 4373045898694032551100115)
                  ·
                    refine ⟨6559568848041048826650173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4373045898694032551100115 6559568848041048826650173)
                    ·
                      refine ⟨2459838318015393309993815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559568848041048826650173 2459838318015393309993815)
                      ·
                        rfl

theorem cell23_4790518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4790518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790518 prefixEnd_4790518 := by exact prefixLift 4790518
  have htrace : WordTrace (prefixWord ++ tailWord_4790518) baseStart_4790518 baseEnd_4790518 := by
    simpa [prefixWord, tailWord_4790518, baseEnd_4790518] using wordTrace_append hprefix tailTrace_4790518
  have hstable : (prefixWord ++ tailWord_4790518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790518).length < 2 ^ (prefixWord ++ tailWord_4790518).sum := by decide
  have hdescent : baseEnd_4790518 < baseStart_4790518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790545 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 1, 3, 2]
def baseStart_4790545 : Nat := 118140960795 + 4790545 * 2 ^ 59
def prefixEnd_4790545 : Nat := 4983230072969 + 3 ^ 40 * 4790545 * 2
def baseEnd_4790545 : Nat := 2459852181993064704356191

theorem tailTrace_4790545 : CollatzResearch.WordTrace tailWord_4790545 prefixEnd_4790545 2459852181993064704356191 := by
  unfold tailWord_4790545
  simp only [CollatzResearch.WordTrace]
  refine ⟨174725530429681099794069089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116483686953120733196046059 174725530429681099794069089)
  ·
    refine ⟨131044147822260824845551817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174725530429681099794069089 131044147822260824845551817)
    ·
      refine ⟨98283110866695618634163863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131044147822260824845551817 98283110866695618634163863)
      ·
        refine ⟨147424666300043427951245795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98283110866695618634163863 147424666300043427951245795)
        ·
          refine ⟨221136999450065141926868693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147424666300043427951245795 221136999450065141926868693)
          ·
            refine ⟨5182898424610901763910985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 221136999450065141926868693 5182898424610901763910985)
            ·
              refine ⟨3887173818458176322933239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5182898424610901763910985 3887173818458176322933239)
              ·
                refine ⟨5830760727687264484399859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887173818458176322933239 5830760727687264484399859)
                ·
                  refine ⟨8746141091530896726599789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830760727687264484399859 8746141091530896726599789)
                  ·
                    refine ⟨3279802909324086272474921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8746141091530896726599789 3279802909324086272474921)
                    ·
                      refine ⟨2459852181993064704356191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3279802909324086272474921 2459852181993064704356191)
                      ·
                        rfl

theorem cell23_4790545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_4790545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790545 prefixEnd_4790545 := by exact prefixLift 4790545
  have htrace : WordTrace (prefixWord ++ tailWord_4790545) baseStart_4790545 baseEnd_4790545 := by
    simpa [prefixWord, tailWord_4790545, baseEnd_4790545] using wordTrace_append hprefix tailTrace_4790545
  have hstable : (prefixWord ++ tailWord_4790545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790545).length < 2 ^ (prefixWord ++ tailWord_4790545).sum := by decide
  have hdescent : baseEnd_4790545 < baseStart_4790545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790564 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 7]
def baseStart_4790564 : Nat := 118140960795 + 4790564 * 2 ^ 59
def prefixEnd_4790564 : Nat := 4983230072969 + 3 ^ 40 * 4790564 * 2
def baseEnd_4790564 : Nat := 273317993125055570002067

theorem tailTrace_4790564 : CollatzResearch.WordTrace tailWord_4790564 prefixEnd_4790564 273317993125055570002067 := by
  unfold tailWord_4790564
  simp only [CollatzResearch.WordTrace]
  refine ⟨87363111708306133019505373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116484148944408177359340497 87363111708306133019505373)
  ·
    refine ⟨32761166890614799882314515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87363111708306133019505373 32761166890614799882314515)
    ·
      refine ⟨49141750335922199823471773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32761166890614799882314515 49141750335922199823471773)
      ·
        refine ⟨18428156375970824933801915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49141750335922199823471773 18428156375970824933801915)
        ·
          refine ⟨27642234563956237400702873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18428156375970824933801915 27642234563956237400702873)
          ·
            refine ⟨20731675922967178050527155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27642234563956237400702873 20731675922967178050527155)
            ·
              refine ⟨31097513884450767075790733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20731675922967178050527155 31097513884450767075790733)
              ·
                refine ⟨11661567706669037653421525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31097513884450767075790733 11661567706669037653421525)
                ·
                  refine ⟨273317993125055570002067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11661567706669037653421525 273317993125055570002067)
                  ·
                    rfl

theorem cell23_4790564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_4790564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790564 prefixEnd_4790564 := by exact prefixLift 4790564
  have htrace : WordTrace (prefixWord ++ tailWord_4790564) baseStart_4790564 baseEnd_4790564 := by
    simpa [prefixWord, tailWord_4790564, baseEnd_4790564] using wordTrace_append hprefix tailTrace_4790564
  have hstable : (prefixWord ++ tailWord_4790564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790564).length < 2 ^ (prefixWord ++ tailWord_4790564).sum := by decide
  have hdescent : baseEnd_4790564 < baseStart_4790564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790604 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4790604 : Nat := 118140960795 + 4790604 * 2 ^ 59
def prefixEnd_4790604 : Nat := 4983230072969 + 3 ^ 40 * 4790604 * 2
def baseEnd_4790604 : Nat := 2459882477351679973518419

theorem tailTrace_4790604 : CollatzResearch.WordTrace tailWord_4790604 prefixEnd_4790604 2459882477351679973518419 := by
  unfold tailWord_4790604
  simp only [CollatzResearch.WordTrace]
  refine ⟨87363841168233676435233433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116485121557644901913644577 87363841168233676435233433)
  ·
    refine ⟨65522880876175257326425075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87363841168233676435233433 65522880876175257326425075)
    ·
      refine ⟨98284321314262885989637613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65522880876175257326425075 98284321314262885989637613)
      ·
        refine ⟨36856620492848582246114105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98284321314262885989637613 36856620492848582246114105)
        ·
          refine ⟨27642465369636436684585579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36856620492848582246114105 27642465369636436684585579)
          ·
            refine ⟨41463698054454655026878369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27642465369636436684585579 41463698054454655026878369)
            ·
              refine ⟨31097773540840991270158777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41463698054454655026878369 31097773540840991270158777)
              ·
                refine ⟨23323330155630743452619083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31097773540840991270158777 23323330155630743452619083)
                ·
                  refine ⟨34984995233446115178928625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23323330155630743452619083 34984995233446115178928625)
                  ·
                    refine ⟨26238746425084586384196469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34984995233446115178928625 26238746425084586384196469)
                    ·
                      refine ⟨2459882477351679973518419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26238746425084586384196469 2459882477351679973518419)
                      ·
                        rfl

theorem cell23_4790604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4790604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790604 prefixEnd_4790604 := by exact prefixLift 4790604
  have htrace : WordTrace (prefixWord ++ tailWord_4790604) baseStart_4790604 baseEnd_4790604 := by
    simpa [prefixWord, tailWord_4790604, baseEnd_4790604] using wordTrace_append hprefix tailTrace_4790604
  have hstable : (prefixWord ++ tailWord_4790604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790604).length < 2 ^ (prefixWord ++ tailWord_4790604).sum := by decide
  have hdescent : baseEnd_4790604 < baseStart_4790604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790651 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 3]
def baseStart_4790651 : Nat := 118140960795 + 4790651 * 2 ^ 59
def prefixEnd_4790651 : Nat := 4983230072969 + 3 ^ 40 * 4790651 * 2
def baseEnd_4790651 : Nat := 2459906610942441289630703

theorem tailTrace_4790651 : CollatzResearch.WordTrace tailWord_4790651 prefixEnd_4790651 2459906610942441289630703 := by
  unfold tailWord_4790651
  simp only [CollatzResearch.WordTrace]
  refine ⟨174729396567297079897427807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116486264378198053264951871 174729396567297079897427807)
  ·
    refine ⟨262094094850945619846141711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174729396567297079897427807 262094094850945619846141711)
    ·
      refine ⟨393141142276418429769212567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262094094850945619846141711 393141142276418429769212567)
      ·
        refine ⟨589711713414627644653818851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393141142276418429769212567 589711713414627644653818851)
        ·
          refine ⟨884567570121941466980728277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589711713414627644653818851 884567570121941466980728277)
          ·
            refine ⟨20732052424733003132360819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 884567570121941466980728277 20732052424733003132360819)
            ·
              refine ⟨31098078637099504698541229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20732052424733003132360819 31098078637099504698541229)
              ·
                refine ⟨11661779488912314261952961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31098078637099504698541229 11661779488912314261952961)
                ·
                  refine ⟨8746334616684235696464721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11661779488912314261952961 8746334616684235696464721)
                  ·
                    refine ⟨6559750962513176772348541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8746334616684235696464721 6559750962513176772348541)
                    ·
                      refine ⟨2459906610942441289630703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559750962513176772348541 2459906610942441289630703)
                      ·
                        rfl

theorem cell23_4790651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 3].length) (baseStart_4790651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790651 prefixEnd_4790651 := by exact prefixLift 4790651
  have htrace : WordTrace (prefixWord ++ tailWord_4790651) baseStart_4790651 baseEnd_4790651 := by
    simpa [prefixWord, tailWord_4790651, baseEnd_4790651] using wordTrace_append hprefix tailTrace_4790651
  have hstable : (prefixWord ++ tailWord_4790651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790651).length < 2 ^ (prefixWord ++ tailWord_4790651).sum := by decide
  have hdescent : baseEnd_4790651 < baseStart_4790651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790741 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4790741 : Nat := 118140960795 + 4790741 * 2 ^ 59
def prefixEnd_4790741 : Nat := 4983230072969 + 3 ^ 40 * 4790741 * 2
def baseEnd_4790741 : Nat := 2459952824201345937505289

theorem tailTrace_4790741 : CollatzResearch.WordTrace tailWord_4790741 prefixEnd_4790741 2459952824201345937505289 := by
  unfold tailWord_4790741
  simp only [CollatzResearch.WordTrace]
  refine ⟨174732679136971025268204077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116488452757980683512136051 174732679136971025268204077)
  ·
    refine ⟨65524754676364134475576529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174732679136971025268204077 65524754676364134475576529)
    ·
      refine ⟨49143566007273100856682397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65524754676364134475576529 49143566007273100856682397)
      ·
        refine ⟨18428837252727412821255899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49143566007273100856682397 18428837252727412821255899)
        ·
          refine ⟨27643255879091119231883849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18428837252727412821255899 27643255879091119231883849)
          ·
            refine ⟨20732441909318339423912887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27643255879091119231883849 20732441909318339423912887)
            ·
              refine ⟨31098662863977509135869331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20732441909318339423912887 31098662863977509135869331)
              ·
                refine ⟨46647994295966263703803997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31098662863977509135869331 46647994295966263703803997)
                ·
                  refine ⟨17492997860987348888926499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46647994295966263703803997 17492997860987348888926499)
                  ·
                    refine ⟨26239496791481023333389749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17492997860987348888926499 26239496791481023333389749)
                    ·
                      refine ⟨2459952824201345937505289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26239496791481023333389749 2459952824201345937505289)
                      ·
                        rfl

theorem cell23_4790741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4790741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790741 prefixEnd_4790741 := by exact prefixLift 4790741
  have htrace : WordTrace (prefixWord ++ tailWord_4790741) baseStart_4790741 baseEnd_4790741 := by
    simpa [prefixWord, tailWord_4790741, baseEnd_4790741] using wordTrace_append hprefix tailTrace_4790741
  have hstable : (prefixWord ++ tailWord_4790741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790741).length < 2 ^ (prefixWord ++ tailWord_4790741).sum := by decide
  have hdescent : baseEnd_4790741 < baseStart_4790741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790744 : List Nat := [2, 1, 2, 2, 2, 1, 1, 12]
def baseStart_4790744 : Nat := 118140960795 + 4790744 * 2 ^ 59
def prefixEnd_4790744 : Nat := 4983230072969 + 3 ^ 40 * 4790744 * 2
def baseEnd_4790744 : Nat := 91109420912715163917325

theorem tailTrace_4790744 : CollatzResearch.WordTrace tailWord_4790744 prefixEnd_4790744 91109420912715163917325 := by
  unfold tailWord_4790744
  simp only [CollatzResearch.WordTrace]
  refine ⟨87366394277980078390281643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116488525703973437853708857 87366394277980078390281643)
  ·
    refine ⟨131049591416970117585422465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87366394277980078390281643 131049591416970117585422465)
    ·
      refine ⟨98287193562727588189066849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131049591416970117585422465 98287193562727588189066849)
      ·
        refine ⟨73715395172045691141800137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98287193562727588189066849 73715395172045691141800137)
        ·
          refine ⟨55286546379034268356350103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73715395172045691141800137 55286546379034268356350103)
          ·
            refine ⟨82929819568551402534525155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55286546379034268356350103 82929819568551402534525155)
            ·
              refine ⟨124394729352827103801787733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82929819568551402534525155 124394729352827103801787733)
              ·
                refine ⟨91109420912715163917325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 124394729352827103801787733 91109420912715163917325)
                ·
                  rfl

theorem cell23_4790744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 12].length) (baseStart_4790744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790744 prefixEnd_4790744 := by exact prefixLift 4790744
  have htrace : WordTrace (prefixWord ++ tailWord_4790744) baseStart_4790744 baseEnd_4790744 := by
    simpa [prefixWord, tailWord_4790744, baseEnd_4790744] using wordTrace_append hprefix tailTrace_4790744
  have hstable : (prefixWord ++ tailWord_4790744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790744).length < 2 ^ (prefixWord ++ tailWord_4790744).sum := by decide
  have hdescent : baseEnd_4790744 < baseStart_4790744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790751 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_4790751 : Nat := 118140960795 + 4790751 * 2 ^ 59
def prefixEnd_4790751 : Nat := 4983230072969 + 3 ^ 40 * 4790751 * 2
def baseEnd_4790751 : Nat := 2459957959007890898380243

theorem tailTrace_4790751 : CollatzResearch.WordTrace tailWord_4790751 prefixEnd_4790751 2459957959007890898380243 := by
  unfold tailWord_4790751
  simp only [CollatzResearch.WordTrace]
  refine ⟨174733043866934796976068107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116488695911289864650712071 174733043866934796976068107)
  ·
    refine ⟨262099565800402195464102161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174733043866934796976068107 262099565800402195464102161)
    ·
      refine ⟨196574674350301646598076621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262099565800402195464102161 196574674350301646598076621)
      ·
        refine ⟨73715502881363117474278733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196574674350301646598076621 73715502881363117474278733)
        ·
          refine ⟨27643313580511169052854525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73715502881363117474278733 27643313580511169052854525)
          ·
            refine ⟨10366242592691688394820447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27643313580511169052854525 10366242592691688394820447)
            ·
              refine ⟨15549363889037532592230671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10366242592691688394820447 15549363889037532592230671)
              ·
                refine ⟨23324045833556298888346007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15549363889037532592230671 23324045833556298888346007)
                ·
                  refine ⟨34986068750334448332519011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23324045833556298888346007 34986068750334448332519011)
                  ·
                    refine ⟨52479103125501672498778517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34986068750334448332519011 52479103125501672498778517)
                    ·
                      refine ⟨2459957959007890898380243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52479103125501672498778517 2459957959007890898380243)
                      ·
                        rfl

theorem cell23_4790751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_4790751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790751 prefixEnd_4790751 := by exact prefixLift 4790751
  have htrace : WordTrace (prefixWord ++ tailWord_4790751) baseStart_4790751 baseEnd_4790751 := by
    simpa [prefixWord, tailWord_4790751, baseEnd_4790751] using wordTrace_append hprefix tailTrace_4790751
  have hstable : (prefixWord ++ tailWord_4790751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790751).length < 2 ^ (prefixWord ++ tailWord_4790751).sum := by decide
  have hdescent : baseEnd_4790751 < baseStart_4790751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790755 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4790755 : Nat := 118140960795 + 4790755 * 2 ^ 59
def prefixEnd_4790755 : Nat := 4983230072969 + 3 ^ 40 * 4790755 * 2
def baseEnd_4790755 : Nat := 2459960012930508882730225

theorem tailTrace_4790755 : CollatzResearch.WordTrace tailWord_4790755 prefixEnd_4790755 2459960012930508882730225 := by
  unfold tailWord_4790755
  simp only [CollatzResearch.WordTrace]
  refine ⟨174733189758920305659213719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116488793172613537106142479 174733189758920305659213719)
  ·
    refine ⟨262099784638380458488820579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174733189758920305659213719 262099784638380458488820579)
    ·
      refine ⟨393149676957570687733230869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262099784638380458488820579 393149676957570687733230869)
      ·
        refine ⟨18428891107386125987495197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 393149676957570687733230869 18428891107386125987495197)
        ·
          refine ⟨6910834165269797245310699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18428891107386125987495197 6910834165269797245310699)
          ·
            refine ⟨10366251247904695867966049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6910834165269797245310699 10366251247904695867966049)
            ·
              refine ⟨7774688435928521900974537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10366251247904695867966049 7774688435928521900974537)
              ·
                refine ⟨5831016326946391425730903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7774688435928521900974537 5831016326946391425730903)
                ·
                  refine ⟨8746524490419587138596355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5831016326946391425730903 8746524490419587138596355)
                  ·
                    refine ⟨13119786735629380707894533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8746524490419587138596355 13119786735629380707894533)
                    ·
                      refine ⟨2459960012930508882730225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13119786735629380707894533 2459960012930508882730225)
                      ·
                        rfl

theorem cell23_4790755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4790755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790755 prefixEnd_4790755 := by exact prefixLift 4790755
  have htrace : WordTrace (prefixWord ++ tailWord_4790755) baseStart_4790755 baseEnd_4790755 := by
    simpa [prefixWord, tailWord_4790755, baseEnd_4790755] using wordTrace_append hprefix tailTrace_4790755
  have hstable : (prefixWord ++ tailWord_4790755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790755).length < 2 ^ (prefixWord ++ tailWord_4790755).sum := by decide
  have hdescent : baseEnd_4790755 < baseStart_4790755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790771 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 3]
def baseStart_4790771 : Nat := 118140960795 + 4790771 * 2 ^ 59
def prefixEnd_4790771 : Nat := 4983230072969 + 3 ^ 40 * 4790771 * 2
def baseEnd_4790771 : Nat := 2459968228620980820130151

theorem tailTrace_4790771 : CollatzResearch.WordTrace tailWord_4790771 prefixEnd_4790771 2459968228620980820130151 := by
  unfold tailWord_4790771
  simp only [CollatzResearch.WordTrace]
  refine ⟨174733773326862340391796167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116489182217908226927864111 174733773326862340391796167)
  ·
    refine ⟨262100659990293510587694251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174733773326862340391796167 262100659990293510587694251)
    ·
      refine ⟨393150989985440265881541377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262100659990293510587694251 393150989985440265881541377)
      ·
        refine ⟨294863242489080199411156033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393150989985440265881541377 294863242489080199411156033)
        ·
          refine ⟨221147431866810149558367025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294863242489080199411156033 221147431866810149558367025)
          ·
            refine ⟨165860573900107612168775269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221147431866810149558367025 165860573900107612168775269)
            ·
              refine ⟨31098857606270177281645363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165860573900107612168775269 31098857606270177281645363)
              ·
                refine ⟨46648286409405265922468045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31098857606270177281645363 46648286409405265922468045)
                ·
                  refine ⟨17493107403526974720925517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46648286409405265922468045 17493107403526974720925517)
                  ·
                    refine ⟨6559915276322615520347069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17493107403526974720925517 6559915276322615520347069)
                    ·
                      refine ⟨2459968228620980820130151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559915276322615520347069 2459968228620980820130151)
                      ·
                        rfl

theorem cell23_4790771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_4790771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790771 prefixEnd_4790771 := by exact prefixLift 4790771
  have htrace : WordTrace (prefixWord ++ tailWord_4790771) baseStart_4790771 baseEnd_4790771 := by
    simpa [prefixWord, tailWord_4790771, baseEnd_4790771] using wordTrace_append hprefix tailTrace_4790771
  have hstable : (prefixWord ++ tailWord_4790771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790771).length < 2 ^ (prefixWord ++ tailWord_4790771).sum := by decide
  have hdescent : baseEnd_4790771 < baseStart_4790771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790805 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_4790805 : Nat := 118140960795 + 4790805 * 2 ^ 59
def prefixEnd_4790805 : Nat := 4983230072969 + 3 ^ 40 * 4790805 * 2
def baseEnd_4790805 : Nat := 2459985686963233687104995

theorem tailTrace_4790805 : CollatzResearch.WordTrace tailWord_4790805 prefixEnd_4790805 2459985686963233687104995 := by
  unfold tailWord_4790805
  simp only [CollatzResearch.WordTrace]
  refine ⟨174735013408739164198533869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116490008939159442799022579 174735013408739164198533869)
  ·
    refine ⟨65525630028277186574450201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174735013408739164198533869 65525630028277186574450201)
    ·
      refine ⟨49144222521207889930837651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65525630028277186574450201 49144222521207889930837651)
      ·
        refine ⟨73716333781811834896256477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49144222521207889930837651 73716333781811834896256477)
        ·
          refine ⟨27643625168179438086096179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73716333781811834896256477 27643625168179438086096179)
          ·
            refine ⟨41465437752269157129144269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27643625168179438086096179 41465437752269157129144269)
            ·
              refine ⟨15549539157100933923429101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41465437752269157129144269 15549539157100933923429101)
              ·
                refine ⟨5831077183912850221285913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15549539157100933923429101 5831077183912850221285913)
                ·
                  refine ⟨4373307887934637665964435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5831077183912850221285913 4373307887934637665964435)
                  ·
                    refine ⟨6559961831901956498946653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4373307887934637665964435 6559961831901956498946653)
                    ·
                      refine ⟨2459985686963233687104995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559961831901956498946653 2459985686963233687104995)
                      ·
                        rfl

theorem cell23_4790805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_4790805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790805 prefixEnd_4790805 := by exact prefixLift 4790805
  have htrace : WordTrace (prefixWord ++ tailWord_4790805) baseStart_4790805 baseEnd_4790805 := by
    simpa [prefixWord, tailWord_4790805, baseEnd_4790805] using wordTrace_append hprefix tailTrace_4790805
  have hstable : (prefixWord ++ tailWord_4790805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790805).length < 2 ^ (prefixWord ++ tailWord_4790805).sum := by decide
  have hdescent : baseEnd_4790805 < baseStart_4790805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790831 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 3]
def baseStart_4790831 : Nat := 118140960795 + 4790831 * 2 ^ 59
def prefixEnd_4790831 : Nat := 4983230072969 + 3 ^ 40 * 4790831 * 2
def baseEnd_4790831 : Nat := 2459999037460250585379875

theorem tailTrace_4790831 : CollatzResearch.WordTrace tailWord_4790831 prefixEnd_4790831 2459999037460250585379875 := by
  unfold tailWord_4790831
  simp only [CollatzResearch.WordTrace]
  refine ⟨174735961706644970638980347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116490641137763313759320231 174735961706644970638980347)
  ·
    refine ⟨262103942559967455958470521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174735961706644970638980347 262103942559967455958470521)
    ·
      refine ⟨196577956919975591968852891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262103942559967455958470521 196577956919975591968852891)
      ·
        refine ⟨294866935379963387953279337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196577956919975591968852891 294866935379963387953279337)
        ·
          refine ⟨221150201534972540964959503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294866935379963387953279337 221150201534972540964959503)
          ·
            refine ⟨331725302302458811447439255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221150201534972540964959503 331725302302458811447439255)
            ·
              refine ⟨497587953453688217171158883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331725302302458811447439255 497587953453688217171158883)
              ·
                refine ⟨746381930180532325756738325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497587953453688217171158883 746381930180532325756738325)
                ·
                  refine ⟨34986652977212452769847109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 746381930180532325756738325 34986652977212452769847109)
                  ·
                    refine ⟨6559997433227334894346333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34986652977212452769847109 6559997433227334894346333)
                    ·
                      refine ⟨2459999037460250585379875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6559997433227334894346333 2459999037460250585379875)
                      ·
                        rfl

theorem cell23_4790831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_4790831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790831 prefixEnd_4790831 := by exact prefixLift 4790831
  have htrace : WordTrace (prefixWord ++ tailWord_4790831) baseStart_4790831 baseEnd_4790831 := by
    simpa [prefixWord, tailWord_4790831, baseEnd_4790831] using wordTrace_append hprefix tailTrace_4790831
  have hstable : (prefixWord ++ tailWord_4790831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790831).length < 2 ^ (prefixWord ++ tailWord_4790831).sum := by decide
  have hdescent : baseEnd_4790831 < baseStart_4790831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790858 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_4790858 : Nat := 118140960795 + 4790858 * 2 ^ 59
def prefixEnd_4790858 : Nat := 4983230072969 + 3 ^ 40 * 4790858 * 2
def baseEnd_4790858 : Nat := 2460012901437921979742251

theorem tailTrace_4790858 : CollatzResearch.WordTrace tailWord_4790858 prefixEnd_4790858 2460012901437921979742251 := by
  unfold tailWord_4790858
  simp only [CollatzResearch.WordTrace]
  refine ⟨43684236619386788562553307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116491297651698102833475485 43684236619386788562553307)
  ·
    refine ⟨65526354929080182843829961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43684236619386788562553307 65526354929080182843829961)
    ·
      refine ⟨49144766196810137132872471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65526354929080182843829961 49144766196810137132872471)
      ·
        refine ⟨73717149295215205699308707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49144766196810137132872471 73717149295215205699308707)
        ·
          refine ⟨110575723942822808548963061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73717149295215205699308707 110575723942822808548963061)
          ·
            refine ⟨10366474119639638301465287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110575723942822808548963061 10366474119639638301465287)
            ·
              refine ⟨15549711179459457452197931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10366474119639638301465287 15549711179459457452197931)
              ·
                refine ⟨23324566769189186178296897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15549711179459457452197931 23324566769189186178296897)
                ·
                  refine ⟨17493425076891889633722673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23324566769189186178296897 17493425076891889633722673)
                  ·
                    refine ⟨13120068807668917225292005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17493425076891889633722673 13120068807668917225292005)
                    ·
                      refine ⟨2460012901437921979742251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13120068807668917225292005 2460012901437921979742251)
                      ·
                        rfl

theorem cell23_4790858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_4790858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790858 prefixEnd_4790858 := by exact prefixLift 4790858
  have htrace : WordTrace (prefixWord ++ tailWord_4790858) baseStart_4790858 baseEnd_4790858 := by
    simpa [prefixWord, tailWord_4790858, baseEnd_4790858] using wordTrace_append hprefix tailTrace_4790858
  have hstable : (prefixWord ++ tailWord_4790858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790858).length < 2 ^ (prefixWord ++ tailWord_4790858).sum := by decide
  have hdescent : baseEnd_4790858 < baseStart_4790858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790862 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_4790862 : Nat := 118140960795 + 4790862 * 2 ^ 59
def prefixEnd_4790862 : Nat := 4983230072969 + 3 ^ 40 * 4790862 * 2
def baseEnd_4790862 : Nat := 2460014955360539964092233

theorem tailTrace_4790862 : CollatzResearch.WordTrace tailWord_4790862 prefixEnd_4790862 2460014955360539964092233 := by
  unfold tailWord_4790862
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842136546191582866669855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116491394913021775288905893 21842136546191582866669855)
  ·
    refine ⟨32763204819287374300004783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21842136546191582866669855 32763204819287374300004783)
    ·
      refine ⟨49144807228931061450007175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32763204819287374300004783 49144807228931061450007175)
      ·
        refine ⟨73717210843396592175010763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49144807228931061450007175 73717210843396592175010763)
        ·
          refine ⟨110575816265094888262516145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73717210843396592175010763 110575816265094888262516145)
          ·
            refine ⟨82931862198821166196887109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110575816265094888262516145 82931862198821166196887109)
            ·
              refine ⟨15549724162278968661916333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82931862198821166196887109 15549724162278968661916333)
              ·
                refine ⟨5831146560854613248218625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15549724162278968661916333 5831146560854613248218625)
                ·
                  refine ⟨4373359920640959936163969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5831146560854613248218625 4373359920640959936163969)
                  ·
                    refine ⟨3280019940480719952122977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4373359920640959936163969 3280019940480719952122977)
                    ·
                      refine ⟨2460014955360539964092233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280019940480719952122977 2460014955360539964092233)
                      ·
                        rfl

theorem cell23_4790862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_4790862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790862 prefixEnd_4790862 := by exact prefixLift 4790862
  have htrace : WordTrace (prefixWord ++ tailWord_4790862) baseStart_4790862 baseEnd_4790862 := by
    simpa [prefixWord, tailWord_4790862, baseEnd_4790862] using wordTrace_append hprefix tailTrace_4790862
  have hstable : (prefixWord ++ tailWord_4790862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790862).length < 2 ^ (prefixWord ++ tailWord_4790862).sum := by decide
  have hdescent : baseEnd_4790862 < baseStart_4790862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790868 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 7]
def baseStart_4790868 : Nat := 118140960795 + 4790868 * 2 ^ 59
def prefixEnd_4790868 : Nat := 4983230072969 + 3 ^ 40 * 4790868 * 2
def baseEnd_4790868 : Nat := 273335337360496326735245

theorem tailTrace_4790868 : CollatzResearch.WordTrace tailWord_4790868 prefixEnd_4790868 273335337360496326735245 := by
  unfold tailWord_4790868
  simp only [CollatzResearch.WordTrace]
  refine ⟨87368655603755462979038629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116491540805007283972051505 87368655603755462979038629)
  ·
    refine ⟨16381622925704149308569743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87368655603755462979038629 16381622925704149308569743)
    ·
      refine ⟨24572434388556223962854615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16381622925704149308569743 24572434388556223962854615)
      ·
        refine ⟨36858651582834335944281923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24572434388556223962854615 36858651582834335944281923)
        ·
          refine ⟨55287977374251503916422885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36858651582834335944281923 55287977374251503916422885)
          ·
            refine ⟨10366495757672156984329291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55287977374251503916422885 10366495757672156984329291)
            ·
              refine ⟨15549743636508235476493937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10366495757672156984329291 15549743636508235476493937)
              ·
                refine ⟨11662307727381176607370453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15549743636508235476493937 11662307727381176607370453)
                ·
                  refine ⟨273335337360496326735245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11662307727381176607370453 273335337360496326735245)
                  ·
                    rfl

theorem cell23_4790868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_4790868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790868 prefixEnd_4790868 := by exact prefixLift 4790868
  have htrace : WordTrace (prefixWord ++ tailWord_4790868) baseStart_4790868 baseEnd_4790868 := by
    simpa [prefixWord, tailWord_4790868, baseEnd_4790868] using wordTrace_append hprefix tailTrace_4790868
  have hstable : (prefixWord ++ tailWord_4790868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790868).length < 2 ^ (prefixWord ++ tailWord_4790868).sum := by decide
  have hdescent : baseEnd_4790868 < baseStart_4790868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790891 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5]
def baseStart_4790891 : Nat := 118140960795 + 4790891 * 2 ^ 59
def prefixEnd_4790891 : Nat := 4983230072969 + 3 ^ 40 * 4790891 * 2
def baseEnd_4790891 : Nat := 2460029846299520350629599

theorem tailTrace_4790891 : CollatzResearch.WordTrace tailWord_4790891 prefixEnd_4790891 2460029846299520350629599 := by
  unfold tailWord_4790891
  simp only [CollatzResearch.WordTrace]
  refine ⟨174738150086427600886164527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116492100057618400590776351 174738150086427600886164527)
  ·
    refine ⟨262107225129641401329246791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174738150086427600886164527 262107225129641401329246791)
    ·
      refine ⟨393160837694462101993870187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262107225129641401329246791 393160837694462101993870187)
      ·
        refine ⟨589741256541693152990805281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393160837694462101993870187 589741256541693152990805281)
        ·
          refine ⟨442305942406269864743103961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589741256541693152990805281 442305942406269864743103961)
          ·
            refine ⟨331729456804702398557327971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442305942406269864743103961 331729456804702398557327971)
            ·
              refine ⟨497594185207053597835991957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331729456804702398557327971 497594185207053597835991957)
              ·
                refine ⟨23324727431580637398562123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 497594185207053597835991957 23324727431580637398562123)
                ·
                  refine ⟨34987091147370956097843185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23324727431580637398562123 34987091147370956097843185)
                  ·
                    refine ⟨26240318360528217073382389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34987091147370956097843185 26240318360528217073382389)
                    ·
                      refine ⟨2460029846299520350629599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26240318360528217073382389 2460029846299520350629599)
                      ·
                        rfl

theorem cell23_4790891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_4790891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790891 prefixEnd_4790891 := by exact prefixLift 4790891
  have htrace : WordTrace (prefixWord ++ tailWord_4790891) baseStart_4790891 baseEnd_4790891 := by
    simpa [prefixWord, tailWord_4790891, baseEnd_4790891] using wordTrace_append hprefix tailTrace_4790891
  have hstable : (prefixWord ++ tailWord_4790891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790891).length < 2 ^ (prefixWord ++ tailWord_4790891).sum := by decide
  have hdescent : baseEnd_4790891 < baseStart_4790891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790896 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 2, 2, 2]
def baseStart_4790896 : Nat := 118140960795 + 4790896 * 2 ^ 59
def prefixEnd_4790896 : Nat := 4983230072969 + 3 ^ 40 * 4790896 * 2
def baseEnd_4790896 : Nat := 2460032413702792831067077

theorem tailTrace_4790896 : CollatzResearch.WordTrace tailWord_4790896 prefixEnd_4790896 2460032413702792831067077 := by
  unfold tailWord_4790896
  simp only [CollatzResearch.WordTrace]
  refine ⟨87369166225704743370048271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116492221634272991160064361 87369166225704743370048271)
  ·
    refine ⟨131053749338557115055072407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87369166225704743370048271 131053749338557115055072407)
    ·
      refine ⟨196580624007835672582608611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131053749338557115055072407 196580624007835672582608611)
      ·
        refine ⟨294870936011753508873912917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196580624007835672582608611 294870936011753508873912917)
        ·
          refine ⟨3455518781387736432116167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 294870936011753508873912917 3455518781387736432116167)
          ·
            refine ⟨5183278172081604648174251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455518781387736432116167 5183278172081604648174251)
            ·
              refine ⟨7774917258122406972261377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5183278172081604648174251 7774917258122406972261377)
              ·
                refine ⟨5831187943591805229196033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7774917258122406972261377 5831187943591805229196033)
                ·
                  refine ⟨4373390957693853921897025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5831187943591805229196033 4373390957693853921897025)
                  ·
                    refine ⟨3280043218270390441422769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4373390957693853921897025 3280043218270390441422769)
                    ·
                      refine ⟨2460032413702792831067077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280043218270390441422769 2460032413702792831067077)
                      ·
                        rfl

theorem cell23_4790896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 2, 2].length) (baseStart_4790896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790896 prefixEnd_4790896 := by exact prefixLift 4790896
  have htrace : WordTrace (prefixWord ++ tailWord_4790896) baseStart_4790896 baseEnd_4790896 := by
    simpa [prefixWord, tailWord_4790896, baseEnd_4790896] using wordTrace_append hprefix tailTrace_4790896
  have hstable : (prefixWord ++ tailWord_4790896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790896).length < 2 ^ (prefixWord ++ tailWord_4790896).sum := by decide
  have hdescent : baseEnd_4790896 < baseStart_4790896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790931 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6]
def baseStart_4790931 : Nat := 118140960795 + 4790931 * 2 ^ 59
def prefixEnd_4790931 : Nat := 4983230072969 + 3 ^ 40 * 4790931 * 2
def baseEnd_4790931 : Nat := 2460050385525700194129415

theorem tailTrace_4790931 : CollatzResearch.WordTrace tailWord_4790931 prefixEnd_4790931 2460050385525700194129415 := by
  unfold tailWord_4790931
  simp only [CollatzResearch.WordTrace]
  refine ⟨174739609006282687717620647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116493072670855125145080431 174739609006282687717620647)
  ·
    refine ⟨262109413509424031576430971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174739609006282687717620647 262109413509424031576430971)
    ·
      refine ⟨393164120264136047364646457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262109413509424031576430971 393164120264136047364646457)
      ·
        refine ⟨294873090198102035523484843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393164120264136047364646457 294873090198102035523484843)
        ·
          refine ⟨442309635297153053285227265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294873090198102035523484843 442309635297153053285227265)
          ·
            refine ⟨331732226472864789963920449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442309635297153053285227265 331732226472864789963920449)
            ·
              refine ⟨248799169854648592472940337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331732226472864789963920449 248799169854648592472940337)
              ·
                refine ⟨186599377390986444354705253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248799169854648592472940337 186599377390986444354705253)
                ·
                  refine ⟨34987383260809958316507235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186599377390986444354705253 34987383260809958316507235)
                  ·
                    refine ⟨52481074891214937474760853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34987383260809958316507235 52481074891214937474760853)
                    ·
                      refine ⟨2460050385525700194129415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52481074891214937474760853 2460050385525700194129415)
                      ·
                        rfl

theorem cell23_4790931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_4790931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790931 prefixEnd_4790931 := by exact prefixLift 4790931
  have htrace : WordTrace (prefixWord ++ tailWord_4790931) baseStart_4790931 baseEnd_4790931 := by
    simpa [prefixWord, tailWord_4790931, baseEnd_4790931] using wordTrace_append hprefix tailTrace_4790931
  have hstable : (prefixWord ++ tailWord_4790931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790931).length < 2 ^ (prefixWord ++ tailWord_4790931).sum := by decide
  have hdescent : baseEnd_4790931 < baseStart_4790931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790971 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 11]
def baseStart_4790971 : Nat := 118140960795 + 4790971 * 2 ^ 59
def prefixEnd_4790971 : Nat := 4983230072969 + 3 ^ 40 * 4790971 * 2
def baseEnd_4790971 : Nat := 820023641583960012543077

theorem tailTrace_4790971 : CollatzResearch.WordTrace tailWord_4790971 prefixEnd_4790971 820023641583960012543077 := by
  unfold tailWord_4790971
  simp only [CollatzResearch.WordTrace]
  refine ⟨174741067926137774549076767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116494045284091849699384511 174741067926137774549076767)
  ·
    refine ⟨262111601889206661823615151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174741067926137774549076767 262111601889206661823615151)
    ·
      refine ⟨393167402833809992735422727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262111601889206661823615151 393167402833809992735422727)
      ·
        refine ⟨589751104250714989103134091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393167402833809992735422727 589751104250714989103134091)
        ·
          refine ⟨884626656376072483654701137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589751104250714989103134091 884626656376072483654701137)
          ·
            refine ⟨663469992282054362741025853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884626656376072483654701137 663469992282054362741025853)
            ·
              refine ⟨248801247105770386027884695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663469992282054362741025853 248801247105770386027884695)
              ·
                refine ⟨373201870658655579041827043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248801247105770386027884695 373201870658655579041827043)
                ·
                  refine ⟨559802805987983368562740565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373201870658655579041827043 559802805987983368562740565)
                  ·
                    refine ⟨820023641583960012543077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 559802805987983368562740565 820023641583960012543077)
                    ·
                      rfl

theorem cell23_4790971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_4790971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790971 prefixEnd_4790971 := by exact prefixLift 4790971
  have htrace : WordTrace (prefixWord ++ tailWord_4790971) baseStart_4790971 baseEnd_4790971 := by
    simpa [prefixWord, tailWord_4790971, baseEnd_4790971] using wordTrace_append hprefix tailTrace_4790971
  have hstable : (prefixWord ++ tailWord_4790971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790971).length < 2 ^ (prefixWord ++ tailWord_4790971).sum := by decide
  have hdescent : baseEnd_4790971 < baseStart_4790971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4790975 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 6]
def baseStart_4790975 : Nat := 118140960795 + 4790975 * 2 ^ 59
def prefixEnd_4790975 : Nat := 4983230072969 + 3 ^ 40 * 4790975 * 2
def baseEnd_4790975 : Nat := 273341442074944224664357

theorem tailTrace_4790975 : CollatzResearch.WordTrace tailWord_4790975 prefixEnd_4790975 273341442074944224664357 := by
  unfold tailWord_4790975
  simp only [CollatzResearch.WordTrace]
  refine ⟨174741213818123283232222379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116494142545415522154814919 174741213818123283232222379)
  ·
    refine ⟨262111820727184924848333569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174741213818123283232222379 262111820727184924848333569)
    ·
      refine ⟨196583865545388693636250177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262111820727184924848333569 196583865545388693636250177)
      ·
        refine ⟨147437899159041520227187633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196583865545388693636250177 147437899159041520227187633)
        ·
          refine ⟨110578424369281140170390725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147437899159041520227187633 110578424369281140170390725)
          ·
            refine ⟨20733454569240213781948261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110578424369281140170390725 20733454569240213781948261)
            ·
              refine ⟨3887522731732540084115299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20733454569240213781948261 3887522731732540084115299)
              ·
                refine ⟨5831284097598810126172949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887522731732540084115299 5831284097598810126172949)
                ·
                  refine ⟨273341442074944224664357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5831284097598810126172949 273341442074944224664357)
                  ·
                    rfl

theorem cell23_4790975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 6].length) (baseStart_4790975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4790975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4790975 prefixEnd_4790975 := by exact prefixLift 4790975
  have htrace : WordTrace (prefixWord ++ tailWord_4790975) baseStart_4790975 baseEnd_4790975 := by
    simpa [prefixWord, tailWord_4790975, baseEnd_4790975] using wordTrace_append hprefix tailTrace_4790975
  have hstable : (prefixWord ++ tailWord_4790975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4790975).length < 2 ^ (prefixWord ++ tailWord_4790975).sum := by decide
  have hdescent : baseEnd_4790975 < baseStart_4790975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4790975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791012 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_4791012 : Nat := 118140960795 + 4791012 * 2 ^ 59
def prefixEnd_4791012 : Nat := 4983230072969 + 3 ^ 40 * 4791012 * 2
def baseEnd_4791012 : Nat := 2460091977458714377216543

theorem tailTrace_4791012 : CollatzResearch.WordTrace tailWord_4791012 prefixEnd_4791012 2460091977458714377216543 := by
  unfold tailWord_4791012
  simp only [CollatzResearch.WordTrace]
  refine ⟨87371281659494619275659645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116495042212659492367546193 87371281659494619275659645)
  ·
    refine ⟨32764230622310482228372367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87371281659494619275659645 32764230622310482228372367)
    ·
      refine ⟨49146345933465723342558551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32764230622310482228372367 49146345933465723342558551)
      ·
        refine ⟨73719518900198585013837827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49146345933465723342558551 73719518900198585013837827)
        ·
          refine ⟨110579278350297877520756741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73719518900198585013837827 110579278350297877520756741)
          ·
            refine ⟨20733614690680852035141889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110579278350297877520756741 20733614690680852035141889)
            ·
              refine ⟨15550211018010639026356417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20733614690680852035141889 15550211018010639026356417)
              ·
                refine ⟨11662658263507979269767313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15550211018010639026356417 11662658263507979269767313)
                ·
                  refine ⟨8746993697630984452325485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11662658263507979269767313 8746993697630984452325485)
                  ·
                    refine ⟨3280122636611619169622057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8746993697630984452325485 3280122636611619169622057)
                    ·
                      refine ⟨2460091977458714377216543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280122636611619169622057 2460091977458714377216543)
                      ·
                        rfl

theorem cell23_4791012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_4791012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791012 prefixEnd_4791012 := by exact prefixLift 4791012
  have htrace : WordTrace (prefixWord ++ tailWord_4791012) baseStart_4791012 baseEnd_4791012 := by
    simpa [prefixWord, tailWord_4791012, baseEnd_4791012] using wordTrace_append hprefix tailTrace_4791012
  have hstable : (prefixWord ++ tailWord_4791012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791012).length < 2 ^ (prefixWord ++ tailWord_4791012).sum := by decide
  have hdescent : baseEnd_4791012 < baseStart_4791012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791018 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_4791018 : Nat := 118140960795 + 4791018 * 2 ^ 59
def prefixEnd_4791018 : Nat := 4983230072969 + 3 ^ 40 * 4791018 * 2
def baseEnd_4791018 : Nat := 820031686114213784580505

theorem tailTrace_4791018 : CollatzResearch.WordTrace tailWord_4791018 prefixEnd_4791018 820031686114213784580505 := by
  unfold tailWord_4791018
  simp only [CollatzResearch.WordTrace]
  refine ⟨43685695539241875394009427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116495188104645001050691805 43685695539241875394009427)
  ·
    refine ⟨65528543308862813091014141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43685695539241875394009427 65528543308862813091014141)
    ·
      refine ⟨24573203740823554909130303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65528543308862813091014141 24573203740823554909130303)
      ·
        refine ⟨36859805611235332363695455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24573203740823554909130303 36859805611235332363695455)
        ·
          refine ⟨55289708416852998545543183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36859805611235332363695455 55289708416852998545543183)
          ·
            refine ⟨82934562625279497818314775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55289708416852998545543183 82934562625279497818314775)
            ·
              refine ⟨124401843937919246727472163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82934562625279497818314775 124401843937919246727472163)
              ·
                refine ⟨186602765906878870091208245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124401843937919246727472163 186602765906878870091208245)
                ·
                  refine ⟨17494009303769894071050773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186602765906878870091208245 17494009303769894071050773)
                  ·
                    refine ⟨820031686114213784580505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17494009303769894071050773 820031686114213784580505)
                    ·
                      rfl

theorem cell23_4791018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_4791018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791018 prefixEnd_4791018 := by exact prefixLift 4791018
  have htrace : WordTrace (prefixWord ++ tailWord_4791018) baseStart_4791018 baseEnd_4791018 := by
    simpa [prefixWord, tailWord_4791018, baseEnd_4791018] using wordTrace_append hprefix tailTrace_4791018
  have hstable : (prefixWord ++ tailWord_4791018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791018).length < 2 ^ (prefixWord ++ tailWord_4791018).sum := by decide
  have hdescent : baseEnd_4791018 < baseStart_4791018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791042 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_4791042 : Nat := 118140960795 + 4791042 * 2 ^ 59
def prefixEnd_4791042 : Nat := 4983230072969 + 3 ^ 40 * 4791042 * 2
def baseEnd_4791042 : Nat := 2460107381878349259841405

theorem tailTrace_4791042 : CollatzResearch.WordTrace tailWord_4791042 prefixEnd_4791042 2460107381878349259841405 := by
  unfold tailWord_4791042
  simp only [CollatzResearch.WordTrace]
  refine ⟨43685914377220138418727845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116495771672587035783274253 43685914377220138418727845)
  ·
    refine ⟨8191108945728775953511471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43685914377220138418727845 8191108945728775953511471)
    ·
      refine ⟨12286663418593163930267207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8191108945728775953511471 12286663418593163930267207)
      ·
        refine ⟨18429995127889745895400811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12286663418593163930267207 18429995127889745895400811)
        ·
          refine ⟨27644992691834618843101217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18429995127889745895400811 27644992691834618843101217)
          ·
            refine ⟨20733744518875964132325913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27644992691834618843101217 20733744518875964132325913)
            ·
              refine ⟨15550308389156973099244435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20733744518875964132325913 15550308389156973099244435)
              ·
                refine ⟨23325462583735459648866653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15550308389156973099244435 23325462583735459648866653)
                ·
                  refine ⟨8747048468900797368324995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23325462583735459648866653 8747048468900797368324995)
                  ·
                    refine ⟨13120572703351196052487493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8747048468900797368324995 13120572703351196052487493)
                    ·
                      refine ⟨2460107381878349259841405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13120572703351196052487493 2460107381878349259841405)
                      ·
                        rfl

theorem cell23_4791042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_4791042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791042 prefixEnd_4791042 := by exact prefixLift 4791042
  have htrace : WordTrace (prefixWord ++ tailWord_4791042) baseStart_4791042 baseEnd_4791042 := by
    simpa [prefixWord, tailWord_4791042, baseEnd_4791042] using wordTrace_append hprefix tailTrace_4791042
  have hstable : (prefixWord ++ tailWord_4791042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791042).length < 2 ^ (prefixWord ++ tailWord_4791042).sum := by decide
  have hdescent : baseEnd_4791042 < baseStart_4791042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791069 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_4791069 : Nat := 118140960795 + 4791069 * 2 ^ 59
def prefixEnd_4791069 : Nat := 4983230072969 + 3 ^ 40 * 4791069 * 2
def baseEnd_4791069 : Nat := 820040415285340218067927

theorem tailTrace_4791069 : CollatzResearch.WordTrace tailWord_4791069 prefixEnd_4791069 820040415285340218067927 := by
  unfold tailWord_4791069
  simp only [CollatzResearch.WordTrace]
  refine ⟨174744642279782737286144261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116496428186521824857429507 174744642279782737286144261)
  ·
    refine ⟨32764620427459263241152049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174744642279782737286144261 32764620427459263241152049)
    ·
      refine ⟨24573465320594447430864037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32764620427459263241152049 24573465320594447430864037)
      ·
        refine ⟨4607524747611458893287007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24573465320594447430864037 4607524747611458893287007)
        ·
          refine ⟨6911287121417188339930511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4607524747611458893287007 6911287121417188339930511)
          ·
            refine ⟨10366930682125782509895767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6911287121417188339930511 10366930682125782509895767)
            ·
              refine ⟨15550396023188673764843651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10366930682125782509895767 15550396023188673764843651)
              ·
                refine ⟨23325594034783010647265477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15550396023188673764843651 23325594034783010647265477)
                ·
                  refine ⟨4373548881521814496362277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23325594034783010647265477 4373548881521814496362277)
                  ·
                    refine ⟨820040415285340218067927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373548881521814496362277 820040415285340218067927)
                    ·
                      rfl

theorem cell23_4791069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_4791069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791069 prefixEnd_4791069 := by exact prefixLift 4791069
  have htrace : WordTrace (prefixWord ++ tailWord_4791069) baseStart_4791069 baseEnd_4791069 := by
    simpa [prefixWord, tailWord_4791069, baseEnd_4791069] using wordTrace_append hprefix tailTrace_4791069
  have hstable : (prefixWord ++ tailWord_4791069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791069).length < 2 ^ (prefixWord ++ tailWord_4791069).sum := by decide
  have hdescent : baseEnd_4791069 < baseStart_4791069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791076 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_4791076 : Nat := 118140960795 + 4791076 * 2 ^ 59
def prefixEnd_4791076 : Nat := 4983230072969 + 3 ^ 40 * 4791076 * 2
def baseEnd_4791076 : Nat := 2460124840220602126816249

theorem tailTrace_4791076 : CollatzResearch.WordTrace tailWord_4791076 prefixEnd_4791076 2460124840220602126816249 := by
  unfold tailWord_4791076
  simp only [CollatzResearch.WordTrace]
  refine ⟨87372448795378688740824541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116496598393838251654432721 87372448795378688740824541)
  ·
    refine ⟨32764668298267008277809203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87372448795378688740824541 32764668298267008277809203)
    ·
      refine ⟨49147002447400512416713805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32764668298267008277809203 49147002447400512416713805)
      ·
        refine ⟨18430125917775192156267677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49147002447400512416713805 18430125917775192156267677)
        ·
          refine ⟨6911297219165697058600379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18430125917775192156267677 6911297219165697058600379)
          ·
            refine ⟨10366945828748545587900569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6911297219165697058600379 10366945828748545587900569)
            ·
              refine ⟨7775209371561409190925427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10366945828748545587900569 7775209371561409190925427)
              ·
                refine ⟨11662814057342113786388141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7775209371561409190925427 11662814057342113786388141)
                ·
                  refine ⟨4373555271503292669895553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11662814057342113786388141 4373555271503292669895553)
                  ·
                    refine ⟨3280166453627469502421665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4373555271503292669895553 3280166453627469502421665)
                    ·
                      refine ⟨2460124840220602126816249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280166453627469502421665 2460124840220602126816249)
                      ·
                        rfl

theorem cell23_4791076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_4791076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791076 prefixEnd_4791076 := by exact prefixLift 4791076
  have htrace : WordTrace (prefixWord ++ tailWord_4791076) baseStart_4791076 baseEnd_4791076 := by
    simpa [prefixWord, tailWord_4791076, baseEnd_4791076] using wordTrace_append hprefix tailTrace_4791076
  have hstable : (prefixWord ++ tailWord_4791076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791076).length < 2 ^ (prefixWord ++ tailWord_4791076).sum := by decide
  have hdescent : baseEnd_4791076 < baseStart_4791076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791086 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_4791086 : Nat := 118140960795 + 4791086 * 2 ^ 59
def prefixEnd_4791086 : Nat := 4983230072969 + 3 ^ 40 * 4791086 * 2
def baseEnd_4791086 : Nat := 820043325009049029230401

theorem tailTrace_4791086 : CollatzResearch.WordTrace tailWord_4791086 prefixEnd_4791086 820043325009049029230401 := by
  unfold tailWord_4791086
  simp only [CollatzResearch.WordTrace]
  refine ⟨21843157790090143648689139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116496841547147432793008741 21843157790090143648689139)
  ·
    refine ⟨32764736685135215473033709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21843157790090143648689139 32764736685135215473033709)
    ·
      refine ⟨12286776256925705802387641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32764736685135215473033709 12286776256925705802387641)
      ·
        refine ⟨9215082192694279351790731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12286776256925705802387641 9215082192694279351790731)
        ·
          refine ⟨13822623289041419027686097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9215082192694279351790731 13822623289041419027686097)
          ·
            refine ⟨10366967466781064270764573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13822623289041419027686097 10366967466781064270764573)
            ·
              refine ⟨3887612800042899101536715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10366967466781064270764573 3887612800042899101536715)
              ·
                refine ⟨5831419200064348652305073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887612800042899101536715 5831419200064348652305073)
                ·
                  refine ⟨4373564400048261489228805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5831419200064348652305073 4373564400048261489228805)
                  ·
                    refine ⟨820043325009049029230401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373564400048261489228805 820043325009049029230401)
                    ·
                      rfl

theorem cell23_4791086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_4791086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791086 prefixEnd_4791086 := by exact prefixLift 4791086
  have htrace : WordTrace (prefixWord ++ tailWord_4791086) baseStart_4791086 baseEnd_4791086 := by
    simpa [prefixWord, tailWord_4791086, baseEnd_4791086] using wordTrace_append hprefix tailTrace_4791086
  have hstable : (prefixWord ++ tailWord_4791086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791086).length < 2 ^ (prefixWord ++ tailWord_4791086).sum := by decide
  have hdescent : baseEnd_4791086 < baseStart_4791086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791088 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_4791088 : Nat := 118140960795 + 4791088 * 2 ^ 59
def prefixEnd_4791088 : Nat := 4983230072969 + 3 ^ 40 * 4791088 * 2
def baseEnd_4791088 : Nat := 2460131001988456079866193

theorem tailTrace_4791088 : CollatzResearch.WordTrace tailWord_4791088 prefixEnd_4791088 2460131001988456079866193 := by
  unfold tailWord_4791088
  simp only [CollatzResearch.WordTrace]
  refine ⟨87372667633356951765542959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116496890177809269020723945 87372667633356951765542959)
  ·
    refine ⟨131059001450035427648314439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87372667633356951765542959 131059001450035427648314439)
    ·
      refine ⟨196588502175053141472471659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131059001450035427648314439 196588502175053141472471659)
      ·
        refine ⟨294882753262579712208707489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196588502175053141472471659 294882753262579712208707489)
        ·
          refine ⟨221162064946934784156530617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294882753262579712208707489 221162064946934784156530617)
          ·
            refine ⟨165871548710201088117397963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221162064946934784156530617 165871548710201088117397963)
            ·
              refine ⟨248807323065301632176096945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165871548710201088117397963 248807323065301632176096945)
              ·
                refine ⟨186605492298976224132072709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248807323065301632176096945 186605492298976224132072709)
                ·
                  refine ⟨34988529806058042024763633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186605492298976224132072709 34988529806058042024763633)
                  ·
                    refine ⟨26241397354543531518572725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34988529806058042024763633 26241397354543531518572725)
                    ·
                      refine ⟨2460131001988456079866193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26241397354543531518572725 2460131001988456079866193)
                      ·
                        rfl

theorem cell23_4791088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_4791088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791088 prefixEnd_4791088 := by exact prefixLift 4791088
  have htrace : WordTrace (prefixWord ++ tailWord_4791088) baseStart_4791088 baseEnd_4791088 := by
    simpa [prefixWord, tailWord_4791088, baseEnd_4791088] using wordTrace_append hprefix tailTrace_4791088
  have hstable : (prefixWord ++ tailWord_4791088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791088).length < 2 ^ (prefixWord ++ tailWord_4791088).sum := by decide
  have hdescent : baseEnd_4791088 < baseStart_4791088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791135 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 3]
def baseStart_4791135 : Nat := 118140960795 + 4791135 * 2 ^ 59
def prefixEnd_4791135 : Nat := 4983230072969 + 3 ^ 40 * 4791135 * 2
def baseEnd_4791135 : Nat := 2460155135579217395978477

theorem tailTrace_4791135 : CollatzResearch.WordTrace tailWord_4791135 prefixEnd_4791135 2460155135579217395978477 := by
  unfold tailWord_4791135
  simp only [CollatzResearch.WordTrace]
  refine ⟨174747049497543630558046859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116498032998362420372031239 174747049497543630558046859)
  ·
    refine ⟨262120574246315445837070289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174747049497543630558046859 262120574246315445837070289)
    ·
      refine ⟨196590430684736584377802717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262120574246315445837070289 196590430684736584377802717)
      ·
        refine ⟨73721411506776219141676019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196590430684736584377802717 73721411506776219141676019)
        ·
          refine ⟨110582117260164328712514029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73721411506776219141676019 110582117260164328712514029)
          ·
            refine ⟨41468293972561623267192761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110582117260164328712514029 41468293972561623267192761)
            ·
              refine ⟨31101220479421217450394571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41468293972561623267192761 31101220479421217450394571)
              ·
                refine ⟨46651830719131826175591857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31101220479421217450394571 46651830719131826175591857)
                ·
                  refine ⟨34988873039348869631693893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46651830719131826175591857 34988873039348869631693893)
                  ·
                    refine ⟨6560413694877913055942605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34988873039348869631693893 6560413694877913055942605)
                    ·
                      refine ⟨2460155135579217395978477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6560413694877913055942605 2460155135579217395978477)
                      ·
                        rfl

theorem cell23_4791135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_4791135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791135 prefixEnd_4791135 := by exact prefixLift 4791135
  have htrace : WordTrace (prefixWord ++ tailWord_4791135) baseStart_4791135 baseEnd_4791135 := by
    simpa [prefixWord, tailWord_4791135, baseEnd_4791135] using wordTrace_append hprefix tailTrace_4791135
  have hstable : (prefixWord ++ tailWord_4791135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791135).length < 2 ^ (prefixWord ++ tailWord_4791135).sum := by decide
  have hdescent : baseEnd_4791135 < baseStart_4791135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791172 : List Nat := [2, 3, 2, 1, 1, 1, 1, 7, 5]
def baseStart_4791172 : Nat := 118140960795 + 4791172 * 2 ^ 59
def prefixEnd_4791172 : Nat := 4983230072969 + 3 ^ 40 * 4791172 * 2
def baseEnd_4791172 : Nat := 273352681595937083468423

theorem tailTrace_4791172 : CollatzResearch.WordTrace tailWord_4791172 prefixEnd_4791172 273352681595937083468423 := by
  unfold tailWord_4791172
  simp only [CollatzResearch.WordTrace]
  refine ⟨87374199499204792938571885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116498932665606390584762513 87374199499204792938571885)
  ·
    refine ⟨32765324812201797351964457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87374199499204792938571885 32765324812201797351964457)
    ·
      refine ⟨24573993609151348013973343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32765324812201797351964457 24573993609151348013973343)
      ·
        refine ⟨36860990413727022020960015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24573993609151348013973343 36860990413727022020960015)
        ·
          refine ⟨55291485620590533031440023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36860990413727022020960015 55291485620590533031440023)
          ·
            refine ⟨82937228430885799547160035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55291485620590533031440023 82937228430885799547160035)
            ·
              refine ⟨124405842646328699320740053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82937228430885799547160035 124405842646328699320740053)
              ·
                refine ⟨2915761937023328890329845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124405842646328699320740053 2915761937023328890329845)
                ·
                  refine ⟨273352681595937083468423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2915761937023328890329845 273352681595937083468423)
                  ·
                    rfl

theorem cell23_4791172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_4791172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791172 prefixEnd_4791172 := by exact prefixLift 4791172
  have htrace : WordTrace (prefixWord ++ tailWord_4791172) baseStart_4791172 baseEnd_4791172 := by
    simpa [prefixWord, tailWord_4791172, baseEnd_4791172] using wordTrace_append hprefix tailTrace_4791172
  have hstable : (prefixWord ++ tailWord_4791172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791172).length < 2 ^ (prefixWord ++ tailWord_4791172).sum := by decide
  have hdescent : baseEnd_4791172 < baseStart_4791172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791189 : List Nat := [1, 3, 2, 1, 1, 4, 4, 2, 5]
def baseStart_4791189 : Nat := 118140960795 + 4791189 * 2 ^ 59
def prefixEnd_4791189 : Nat := 4983230072969 + 3 ^ 40 * 4791189 * 2
def baseEnd_4791189 : Nat := 273353651503840020522581

theorem tailTrace_4791189 : CollatzResearch.WordTrace tailWord_4791189 prefixEnd_4791189 273353651503840020522581 := by
  unfold tailWord_4791189
  simp only [CollatzResearch.WordTrace]
  refine ⟨174749019039347997780512621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116499346026231998520341747 174749019039347997780512621)
  ·
    refine ⟨65530882139755499167692233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174749019039347997780512621 65530882139755499167692233)
    ·
      refine ⟨49148161604816624375769175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65530882139755499167692233 49148161604816624375769175)
      ·
        refine ⟨73722242407224936563653763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49148161604816624375769175 73722242407224936563653763)
        ·
          refine ⟨110583363610837404845480645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73722242407224936563653763 110583363610837404845480645)
          ·
            refine ⟨20734380677032013408527621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110583363610837404845480645 20734380677032013408527621)
            ·
              refine ⟨3887696376943502514098929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20734380677032013408527621 3887696376943502514098929)
              ·
                refine ⟨2915772282707626885574197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3887696376943502514098929 2915772282707626885574197)
                ·
                  refine ⟨273353651503840020522581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2915772282707626885574197 273353651503840020522581)
                  ·
                    rfl

theorem cell23_4791189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_4791189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791189 prefixEnd_4791189 := by exact prefixLift 4791189
  have htrace : WordTrace (prefixWord ++ tailWord_4791189) baseStart_4791189 baseEnd_4791189 := by
    simpa [prefixWord, tailWord_4791189, baseEnd_4791189] using wordTrace_append hprefix tailTrace_4791189
  have hstable : (prefixWord ++ tailWord_4791189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791189).length < 2 ^ (prefixWord ++ tailWord_4791189).sum := by decide
  have hdescent : baseEnd_4791189 < baseStart_4791189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791242 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_4791242 : Nat := 118140960795 + 4791242 * 2 ^ 59
def prefixEnd_4791242 : Nat := 4983230072969 + 3 ^ 40 * 4791242 * 2
def baseEnd_4791242 : Nat := 2460210078009248477340485

theorem tailTrace_4791242 : CollatzResearch.WordTrace tailWord_4791242 prefixEnd_4791242 2460210078009248477340485 := by
  unfold tailWord_4791242
  simp only [CollatzResearch.WordTrace]
  refine ⟨43687738027038996958047995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116500634738770658554794653 43687738027038996958047995)
  ·
    refine ⟨65531607040558495437071993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43687738027038996958047995 65531607040558495437071993)
    ·
      refine ⟨49148705280418871577803995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65531607040558495437071993 49148705280418871577803995)
      ·
        refine ⟨73723057920628307366705993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49148705280418871577803995 73723057920628307366705993)
        ·
          refine ⟨55292293440471230525029495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73723057920628307366705993 55292293440471230525029495)
          ·
            refine ⟨82938440160706845787544243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55292293440471230525029495 82938440160706845787544243)
            ·
              refine ⟨124407660241060268681316365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82938440160706845787544243 124407660241060268681316365)
              ·
                refine ⟨46652872590397600755493637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124407660241060268681316365 46652872590397600755493637)
                ·
                  refine ⟨8747413610699550141655057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46652872590397600755493637 8747413610699550141655057)
                  ·
                    refine ⟨6560560208024662606241293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8747413610699550141655057 6560560208024662606241293)
                    ·
                      refine ⟨2460210078009248477340485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6560560208024662606241293 2460210078009248477340485)
                      ·
                        rfl

theorem cell23_4791242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_4791242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791242 prefixEnd_4791242 := by exact prefixLift 4791242
  have htrace : WordTrace (prefixWord ++ tailWord_4791242) baseStart_4791242 baseEnd_4791242 := by
    simpa [prefixWord, tailWord_4791242, baseEnd_4791242] using wordTrace_append hprefix tailTrace_4791242
  have hstable : (prefixWord ++ tailWord_4791242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791242).length < 2 ^ (prefixWord ++ tailWord_4791242).sum := by decide
  have hdescent : baseEnd_4791242 < baseStart_4791242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791249 : List Nat := [1, 2, 2, 1, 2, 1, 3, 6, 1, 4]
def baseStart_4791249 : Nat := 118140960795 + 4791249 * 2 ^ 59
def prefixEnd_4791249 : Nat := 4983230072969 + 3 ^ 40 * 4791249 * 2
def baseEnd_4791249 : Nat := 820071224124609983317651

theorem tailTrace_4791249 : CollatzResearch.WordTrace tailWord_4791249 prefixEnd_4791249 820071224124609983317651 := by
  unfold tailWord_4791249
  simp only [CollatzResearch.WordTrace]
  refine ⟨174751207419130628027696801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116500804946087085351797867 174751207419130628027696801)
  ·
    refine ⟨131063405564347971020772601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174751207419130628027696801 131063405564347971020772601)
    ·
      refine ⟨98297554173260978265579451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131063405564347971020772601 98297554173260978265579451)
      ·
        refine ⟨147446331259891467398369177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98297554173260978265579451 147446331259891467398369177)
        ·
          refine ⟨110584748444918600548776883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147446331259891467398369177 110584748444918600548776883)
          ·
            refine ⟨165877122667377900823165325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110584748444918600548776883 165877122667377900823165325)
            ·
              refine ⟨62203921000266712808686997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165877122667377900823165325 62203921000266712808686997)
              ·
                refine ⟨2915808796887502162907203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62203921000266712808686997 2915808796887502162907203)
                ·
                  refine ⟨4373713195331253244360805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915808796887502162907203 4373713195331253244360805)
                  ·
                    refine ⟨820071224124609983317651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373713195331253244360805 820071224124609983317651)
                    ·
                      rfl

theorem cell23_4791249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_4791249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791249 prefixEnd_4791249 := by exact prefixLift 4791249
  have htrace : WordTrace (prefixWord ++ tailWord_4791249) baseStart_4791249 baseEnd_4791249 := by
    simpa [prefixWord, tailWord_4791249, baseEnd_4791249] using wordTrace_append hprefix tailTrace_4791249
  have hstable : (prefixWord ++ tailWord_4791249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791249).length < 2 ^ (prefixWord ++ tailWord_4791249).sum := by decide
  have hdescent : baseEnd_4791249 < baseStart_4791249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791265 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_4791265 : Nat := 118140960795 + 4791265 * 2 ^ 59
def prefixEnd_4791265 : Nat := 4983230072969 + 3 ^ 40 * 4791265 * 2
def baseEnd_4791265 : Nat := 2460221888064301887352879

theorem tailTrace_4791265 : CollatzResearch.WordTrace tailWord_4791265 prefixEnd_4791265 2460221888064301887352879 := by
  unfold tailWord_4791265
  simp only [CollatzResearch.WordTrace]
  refine ⟨174751790987072662760279249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116501193991381775173519499 174751790987072662760279249)
  ·
    refine ⟨131063843240304497070209437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174751790987072662760279249 131063843240304497070209437)
    ·
      refine ⟨49148941215114186401328539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131063843240304497070209437 49148941215114186401328539)
      ·
        refine ⟨73723411822671279601992809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49148941215114186401328539 73723411822671279601992809)
        ·
          refine ⟨55292558867003459701494607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73723411822671279601992809 55292558867003459701494607)
          ·
            refine ⟨82938838300505189552241911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55292558867003459701494607 82938838300505189552241911)
            ·
              refine ⟨124408257450757784328362867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82938838300505189552241911 124408257450757784328362867)
              ·
                refine ⟨186612386176136676492544301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124408257450757784328362867 186612386176136676492544301)
                ·
                  refine ⟨69979644816051253684704113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186612386176136676492544301 69979644816051253684704113)
                  ·
                    refine ⟨52484733612038440263528085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69979644816051253684704113 52484733612038440263528085)
                    ·
                      refine ⟨2460221888064301887352879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52484733612038440263528085 2460221888064301887352879)
                      ·
                        rfl

theorem cell23_4791265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_4791265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791265 prefixEnd_4791265 := by exact prefixLift 4791265
  have htrace : WordTrace (prefixWord ++ tailWord_4791265) baseStart_4791265 baseEnd_4791265 := by
    simpa [prefixWord, tailWord_4791265, baseEnd_4791265] using wordTrace_append hprefix tailTrace_4791265
  have hstable : (prefixWord ++ tailWord_4791265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791265).length < 2 ^ (prefixWord ++ tailWord_4791265).sum := by decide
  have hdescent : baseEnd_4791265 < baseStart_4791265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791266 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4791266 : Nat := 118140960795 + 4791266 * 2 ^ 59
def prefixEnd_4791266 : Nat := 4983230072969 + 3 ^ 40 * 4791266 * 2
def baseEnd_4791266 : Nat := 820074133848318794480125

theorem tailTrace_4791266 : CollatzResearch.WordTrace tailWord_4791266 prefixEnd_4791266 820074133848318794480125 := by
  unfold tailWord_4791266
  simp only [CollatzResearch.WordTrace]
  refine ⟨43687956865017259982766413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116501218306712693287377101 43687956865017259982766413)
  ·
    refine ⟨16382983824381472493537405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43687956865017259982766413 16382983824381472493537405)
    ·
      refine ⟨6143618934143052185076527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16382983824381472493537405 6143618934143052185076527)
      ·
        refine ⟨9215428401214578277614791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6143618934143052185076527 9215428401214578277614791)
        ·
          refine ⟨13823142601821867416422187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9215428401214578277614791 13823142601821867416422187)
          ·
            refine ⟨20734713902732801124633281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13823142601821867416422187 20734713902732801124633281)
            ·
              refine ⟨15551035427049600843474961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20734713902732801124633281 15551035427049600843474961)
              ·
                refine ⟨11663276570287200632606221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15551035427049600843474961 11663276570287200632606221)
                ·
                  refine ⟨4373728713857700237227333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11663276570287200632606221 4373728713857700237227333)
                  ·
                    refine ⟨820074133848318794480125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373728713857700237227333 820074133848318794480125)
                    ·
                      rfl

theorem cell23_4791266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4791266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791266 prefixEnd_4791266 := by exact prefixLift 4791266
  have htrace : WordTrace (prefixWord ++ tailWord_4791266) baseStart_4791266 baseEnd_4791266 := by
    simpa [prefixWord, tailWord_4791266, baseEnd_4791266] using wordTrace_append hprefix tailTrace_4791266
  have hstable : (prefixWord ++ tailWord_4791266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791266).length < 2 ^ (prefixWord ++ tailWord_4791266).sum := by decide
  have hdescent : baseEnd_4791266 < baseStart_4791266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791306 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_4791306 : Nat := 118140960795 + 4791306 * 2 ^ 59
def prefixEnd_4791306 : Nat := 4983230072969 + 3 ^ 40 * 4791306 * 2
def baseEnd_4791306 : Nat := 2460242940771136226940191

theorem tailTrace_4791306 : CollatzResearch.WordTrace tailWord_4791306 prefixEnd_4791306 2460242940771136226940191 := by
  unfold tailWord_4791306
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688321594981031690630443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116502190919949417841681181 43688321594981031690630443)
  ·
    refine ⟨65532482392471547535945665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43688321594981031690630443 65532482392471547535945665)
    ·
      refine ⟨49149361794353660651959249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65532482392471547535945665 49149361794353660651959249)
      ·
        refine ⟨36862021345765245488969437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49149361794353660651959249 36862021345765245488969437)
        ·
          refine ⟨13823258004661967058363539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36862021345765245488969437 13823258004661967058363539)
          ·
            refine ⟨20734887006992950587545309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13823258004661967058363539 20734887006992950587545309)
            ·
              refine ⟨7775582627622356470329491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20734887006992950587545309 7775582627622356470329491)
              ·
                refine ⟨11663373941433534705494237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7775582627622356470329491 11663373941433534705494237)
                ·
                  refine ⟨4373765228037575514560339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11663373941433534705494237 4373765228037575514560339)
                  ·
                    refine ⟨6560647842056363271840509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4373765228037575514560339 6560647842056363271840509)
                    ·
                      refine ⟨2460242940771136226940191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6560647842056363271840509 2460242940771136226940191)
                      ·
                        rfl

theorem cell23_4791306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_4791306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791306 prefixEnd_4791306 := by exact prefixLift 4791306
  have htrace : WordTrace (prefixWord ++ tailWord_4791306) baseStart_4791306 baseEnd_4791306 := by
    simpa [prefixWord, tailWord_4791306, baseEnd_4791306] using wordTrace_append hprefix tailTrace_4791306
  have hstable : (prefixWord ++ tailWord_4791306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791306).length < 2 ^ (prefixWord ++ tailWord_4791306).sum := by decide
  have hdescent : baseEnd_4791306 < baseStart_4791306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791322 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_4791322 : Nat := 118140960795 + 4791322 * 2 ^ 59
def prefixEnd_4791322 : Nat := 4983230072969 + 3 ^ 40 * 4791322 * 2
def baseEnd_4791322 : Nat := 820083718820536054780039

theorem tailTrace_4791322 : CollatzResearch.WordTrace tailWord_4791322 prefixEnd_4791322 820083718820536054780039 := by
  unfold tailWord_4791322
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688467486966540373776055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116502579965244107663402813 43688467486966540373776055)
  ·
    refine ⟨65532701230449810560664083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43688467486966540373776055 65532701230449810560664083)
    ·
      refine ⟨98299051845674715840996125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65532701230449810560664083 98299051845674715840996125)
      ·
        refine ⟨36862144442128018440373547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98299051845674715840996125 36862144442128018440373547)
        ·
          refine ⟨55293216663192027660560321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36862144442128018440373547 55293216663192027660560321)
          ·
            refine ⟨41469912497394020745420241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55293216663192027660560321 41469912497394020745420241)
            ·
              refine ⟨31102434373045515559065181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41469912497394020745420241 31102434373045515559065181)
              ·
                refine ⟨11663412889892068334649443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31102434373045515559065181 11663412889892068334649443)
                ·
                  refine ⟨17495119334838102501974165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11663412889892068334649443 17495119334838102501974165)
                  ·
                    refine ⟨820083718820536054780039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17495119334838102501974165 820083718820536054780039)
                    ·
                      rfl

theorem cell23_4791322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_4791322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791322 prefixEnd_4791322 := by exact prefixLift 4791322
  have htrace : WordTrace (prefixWord ++ tailWord_4791322) baseStart_4791322 baseEnd_4791322 := by
    simpa [prefixWord, tailWord_4791322, baseEnd_4791322] using wordTrace_append hprefix tailTrace_4791322
  have hstable : (prefixWord ++ tailWord_4791322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791322).length < 2 ^ (prefixWord ++ tailWord_4791322).sum := by decide
  have hdescent : baseEnd_4791322 < baseStart_4791322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791329 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4791329 : Nat := 118140960795 + 4791329 * 2 ^ 59
def prefixEnd_4791329 : Nat := 4983230072969 + 3 ^ 40 * 4791329 * 2
def baseEnd_4791329 : Nat := 2460254750826189636952585

theorem tailTrace_4791329 : CollatzResearch.WordTrace tailWord_4791329 prefixEnd_4791329 2460254750826189636952585 := by
  unfold tailWord_4791329
  simp only [CollatzResearch.WordTrace]
  refine ⟨174754125258840801690609041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116502750172560534460406027 174754125258840801690609041)
  ·
    refine ⟨131065593944130601267956781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174754125258840801690609041 131065593944130601267956781)
    ·
      refine ⟨49149597729048975475483793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131065593944130601267956781 49149597729048975475483793)
      ·
        refine ⟨36862198296786731606612845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49149597729048975475483793 36862198296786731606612845)
        ·
          refine ⟨13823324361295024352479817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36862198296786731606612845 13823324361295024352479817)
          ·
            refine ⟨10367493270971268264359863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13823324361295024352479817 10367493270971268264359863)
            ·
              refine ⟨15551239906456902396539795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10367493270971268264359863 15551239906456902396539795)
              ·
                refine ⟨23326859859685353594809693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15551239906456902396539795 23326859859685353594809693)
                ·
                  refine ⟨8747572447382007598053635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23326859859685353594809693 8747572447382007598053635)
                  ·
                    refine ⟨13121358671073011397080453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8747572447382007598053635 13121358671073011397080453)
                    ·
                      refine ⟨2460254750826189636952585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13121358671073011397080453 2460254750826189636952585)
                      ·
                        rfl

theorem cell23_4791329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4791329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791329 prefixEnd_4791329 := by exact prefixLift 4791329
  have htrace : WordTrace (prefixWord ++ tailWord_4791329) baseStart_4791329 baseEnd_4791329 := by
    simpa [prefixWord, tailWord_4791329, baseEnd_4791329] using wordTrace_append hprefix tailTrace_4791329
  have hstable : (prefixWord ++ tailWord_4791329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791329).length < 2 ^ (prefixWord ++ tailWord_4791329).sum := by decide
  have hdescent : baseEnd_4791329 < baseStart_4791329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791346 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_4791346 : Nat := 118140960795 + 4791346 * 2 ^ 59
def prefixEnd_4791346 : Nat := 4983230072969 + 3 ^ 40 * 4791346 * 2
def baseEnd_4791346 : Nat := 2460263479997316070440007

theorem tailTrace_4791346 : CollatzResearch.WordTrace tailWord_4791346 prefixEnd_4791346 2460263479997316070440007 := by
  unfold tailWord_4791346
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688686324944803398494473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116503163533186142395985261 43688686324944803398494473)
  ·
    refine ⟨32766514743708602548870855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43688686324944803398494473 32766514743708602548870855)
    ·
      refine ⟨49149772115562903823306283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32766514743708602548870855 49149772115562903823306283)
      ·
        refine ⟨73724658173344355734959425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49149772115562903823306283 73724658173344355734959425)
        ·
          refine ⟨55293493630008266801219569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73724658173344355734959425 55293493630008266801219569)
          ·
            refine ⟨41470120222506200100914677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55293493630008266801219569 41470120222506200100914677)
            ·
              refine ⟨3887823770859956259460751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41470120222506200100914677 3887823770859956259460751)
              ·
                refine ⟨5831735656289934389191127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887823770859956259460751 5831735656289934389191127)
                ·
                  refine ⟨8747603484434901583786691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5831735656289934389191127 8747603484434901583786691)
                  ·
                    refine ⟨13121405226652352375680037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8747603484434901583786691 13121405226652352375680037)
                    ·
                      refine ⟨2460263479997316070440007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13121405226652352375680037 2460263479997316070440007)
                      ·
                        rfl

theorem cell23_4791346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_4791346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791346 prefixEnd_4791346 := by exact prefixLift 4791346
  have htrace : WordTrace (prefixWord ++ tailWord_4791346) baseStart_4791346 baseEnd_4791346 := by
    simpa [prefixWord, tailWord_4791346, baseEnd_4791346] using wordTrace_append hprefix tailTrace_4791346
  have hstable : (prefixWord ++ tailWord_4791346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791346).length < 2 ^ (prefixWord ++ tailWord_4791346).sum := by decide
  have hdescent : baseEnd_4791346 < baseStart_4791346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791356 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_4791356 : Nat := 118140960795 + 4791356 * 2 ^ 59
def prefixEnd_4791356 : Nat := 4983230072969 + 3 ^ 40 * 4791356 * 2
def baseEnd_4791356 : Nat := 820089538267953677104987

theorem tailTrace_4791356 : CollatzResearch.WordTrace tailWord_4791356 prefixEnd_4791356 820089538267953677104987 := by
  unfold tailWord_4791356
  simp only [CollatzResearch.WordTrace]
  refine ⟨87377555014871492650920961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116503406686495323534561281 87377555014871492650920961)
  ·
    refine ⟨65533166261153619488190721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87377555014871492650920961 65533166261153619488190721)
    ·
      refine ⟨49149874695865214616143041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65533166261153619488190721 49149874695865214616143041)
      ·
        refine ⟨36862406021898910962107281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49149874695865214616143041 36862406021898910962107281)
        ·
          refine ⟨27646804516424183221580461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36862406021898910962107281 27646804516424183221580461)
          ·
            refine ⟨10367551693659068708092673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27646804516424183221580461 10367551693659068708092673)
            ·
              refine ⟨7775663770244301531069505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10367551693659068708092673 7775663770244301531069505)
              ·
                refine ⟨5831747827683226148302129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7775663770244301531069505 5831747827683226148302129)
                ·
                  refine ⟨4373810870762419611226597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5831747827683226148302129 4373810870762419611226597)
                  ·
                    refine ⟨820089538267953677104987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4373810870762419611226597 820089538267953677104987)
                    ·
                      rfl

theorem cell23_4791356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_4791356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791356 prefixEnd_4791356 := by exact prefixLift 4791356
  have htrace : WordTrace (prefixWord ++ tailWord_4791356) baseStart_4791356 baseEnd_4791356 := by
    simpa [prefixWord, tailWord_4791356, baseEnd_4791356] using wordTrace_append hprefix tailTrace_4791356
  have hstable : (prefixWord ++ tailWord_4791356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791356).length < 2 ^ (prefixWord ++ tailWord_4791356).sum := by decide
  have hdescent : baseEnd_4791356 < baseStart_4791356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791363 : List Nat := [1, 1, 1, 3, 1, 2, 5, 4, 1, 2, 2]
def baseStart_4791363 : Nat := 118140960795 + 4791363 * 2 ^ 59
def prefixEnd_4791363 : Nat := 4983230072969 + 3 ^ 40 * 4791363 * 2
def baseEnd_4791363 : Nat := 2460272209168442503927429

theorem tailTrace_4791363 : CollatzResearch.WordTrace tailWord_4791363 prefixEnd_4791363 2460272209168442503927429 := by
  unfold tailWord_4791363
  simp only [CollatzResearch.WordTrace]
  refine ⟨174755365340717625497346743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116503576893811750331564495 174755365340717625497346743)
  ·
    refine ⟨262133048011076438246020115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174755365340717625497346743 262133048011076438246020115)
    ·
      refine ⟨393199572016614657369030173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262133048011076438246020115 393199572016614657369030173)
      ·
        refine ⟨147449839506230496513386315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393199572016614657369030173 147449839506230496513386315)
        ·
          refine ⟨221174759259345744770079473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147449839506230496513386315 221174759259345744770079473)
          ·
            refine ⟨165881069444509308577559605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221174759259345744770079473 165881069444509308577559605)
            ·
              refine ⟨15551350260422747679146213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165881069444509308577559605 15551350260422747679146213)
              ·
                refine ⟨2915878173829265189839915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15551350260422747679146213 2915878173829265189839915)
                ·
                  refine ⟨4373817260743897784759873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915878173829265189839915 4373817260743897784759873)
                  ·
                    refine ⟨3280362945557923338569905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4373817260743897784759873 3280362945557923338569905)
                    ·
                      refine ⟨2460272209168442503927429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280362945557923338569905 2460272209168442503927429)
                      ·
                        rfl

theorem cell23_4791363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_4791363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791363 prefixEnd_4791363 := by exact prefixLift 4791363
  have htrace : WordTrace (prefixWord ++ tailWord_4791363) baseStart_4791363 baseEnd_4791363 := by
    simpa [prefixWord, tailWord_4791363, baseEnd_4791363] using wordTrace_append hprefix tailTrace_4791363
  have hstable : (prefixWord ++ tailWord_4791363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791363).length < 2 ^ (prefixWord ++ tailWord_4791363).sum := by decide
  have hdescent : baseEnd_4791363 < baseStart_4791363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791392 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_4791392 : Nat := 118140960795 + 4791392 * 2 ^ 59
def prefixEnd_4791392 : Nat := 4983230072969 + 3 ^ 40 * 4791392 * 2
def baseEnd_4791392 : Nat := 2460287100107422890464795

theorem tailTrace_4791392 : CollatzResearch.WordTrace tailWord_4791392 prefixEnd_4791392 2460287100107422890464795 := by
  unfold tailWord_4791392
  simp only [CollatzResearch.WordTrace]
  refine ⟨87378211528806281725076215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116504282038408375633434953 87378211528806281725076215)
  ·
    refine ⟨131067317293209422587614323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87378211528806281725076215 131067317293209422587614323)
    ·
      refine ⟨196600975939814133881421485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131067317293209422587614323 196600975939814133881421485)
      ·
        refine ⟨73725365977430300205533057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196600975939814133881421485 73725365977430300205533057)
        ·
          refine ⟨55294024483072725154149793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73725365977430300205533057 55294024483072725154149793)
          ·
            refine ⟨41470518362304543865612345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55294024483072725154149793 41470518362304543865612345)
            ·
              refine ⟨31102888771728407899209259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41470518362304543865612345 31102888771728407899209259)
              ·
                refine ⟨46654333157592611848813889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31102888771728407899209259 46654333157592611848813889)
                ·
                  refine ⟨34990749868194458886610417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46654333157592611848813889 34990749868194458886610417)
                  ·
                    refine ⟨26243062401145844164957813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34990749868194458886610417 26243062401145844164957813)
                    ·
                      refine ⟨2460287100107422890464795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26243062401145844164957813 2460287100107422890464795)
                      ·
                        rfl

theorem cell23_4791392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_4791392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791392 prefixEnd_4791392 := by exact prefixLift 4791392
  have htrace : WordTrace (prefixWord ++ tailWord_4791392) baseStart_4791392 baseEnd_4791392 := by
    simpa [prefixWord, tailWord_4791392, baseEnd_4791392] using wordTrace_append hprefix tailTrace_4791392
  have hstable : (prefixWord ++ tailWord_4791392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791392).length < 2 ^ (prefixWord ++ tailWord_4791392).sum := by decide
  have hdescent : baseEnd_4791392 < baseStart_4791392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791419 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 3, 4, 2]
def baseStart_4791419 : Nat := 118140960795 + 4791419 * 2 ^ 59
def prefixEnd_4791419 : Nat := 4983230072969 + 3 ^ 40 * 4791419 * 2
def baseEnd_4791419 : Nat := 2460300964085094284827171

theorem tailTrace_4791419 : CollatzResearch.WordTrace tailWord_4791419 prefixEnd_4791419 2460300964085094284827171 := by
  unfold tailWord_4791419
  simp only [CollatzResearch.WordTrace]
  refine ⟨174757407828514747061385311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116504938552343164707590207 174757407828514747061385311)
  ·
    refine ⟨262136111742772120592077967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174757407828514747061385311 262136111742772120592077967)
    ·
      refine ⟨393204167614158180888116951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262136111742772120592077967 393204167614158180888116951)
      ·
        refine ⟨589806251421237271332175427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393204167614158180888116951 589806251421237271332175427)
        ·
          refine ⟨884709377131855906998263141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589806251421237271332175427 884709377131855906998263141)
          ·
            refine ⟨165883008212222982562174339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 884709377131855906998263141 165883008212222982562174339)
            ·
              refine ⟨248824512318334473843261509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165883008212222982562174339 248824512318334473843261509)
              ·
                refine ⟨46654596059687713845611533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248824512318334473843261509 46654596059687713845611533)
                ·
                  refine ⟨17495473522382892692104325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46654596059687713845611533 17495473522382892692104325)
                  ·
                    refine ⟨3280401285446792379769561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17495473522382892692104325 3280401285446792379769561)
                    ·
                      refine ⟨2460300964085094284827171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280401285446792379769561 2460300964085094284827171)
                      ·
                        rfl

theorem cell23_4791419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4, 2].length) (baseStart_4791419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791419 prefixEnd_4791419 := by exact prefixLift 4791419
  have htrace : WordTrace (prefixWord ++ tailWord_4791419) baseStart_4791419 baseEnd_4791419 := by
    simpa [prefixWord, tailWord_4791419, baseEnd_4791419] using wordTrace_append hprefix tailTrace_4791419
  have hstable : (prefixWord ++ tailWord_4791419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791419).length < 2 ^ (prefixWord ++ tailWord_4791419).sum := by decide
  have hdescent : baseEnd_4791419 < baseStart_4791419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
