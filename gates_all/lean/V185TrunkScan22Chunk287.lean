import V185TrunkScan22Chunk286

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2560092 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2560092 : Nat := 118140960795 + 2560092 * 2 ^ 59
def prefixEnd_2560092 : Nat := 4983230072969 + 3 ^ 40 * 2560092 * 2
def baseEnd_2560092 : Nat := 876371810486868574650905

theorem tailTrace_2560092 : CollatzResearch.WordTrace tailWord_2560092 prefixEnd_2560092 876371810486868574650905 := by
  unfold tailWord_2560092
  simp only [CollatzResearch.WordTrace]
  refine ⟨46687113120615693874569265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62249484160820925166092353 46687113120615693874569265)
  ·
    refine ⟨35015334840461770405926949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46687113120615693874569265 35015334840461770405926949)
    ·
      refine ⟨6565375282586581951111303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35015334840461770405926949 6565375282586581951111303)
      ·
        refine ⟨9848062923879872926666955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6565375282586581951111303 9848062923879872926666955)
        ·
          refine ⟨14772094385819809390000433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9848062923879872926666955 14772094385819809390000433)
          ·
            refine ⟨11079070789364857042500325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14772094385819809390000433 11079070789364857042500325)
            ·
              refine ⟨2077325773005910695468811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11079070789364857042500325 2077325773005910695468811)
              ·
                refine ⟨3115988659508866043203217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077325773005910695468811 3115988659508866043203217)
                ·
                  refine ⟨2336991494631649532402413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3115988659508866043203217 2336991494631649532402413)
                  ·
                    refine ⟨876371810486868574650905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336991494631649532402413 876371810486868574650905)
                    ·
                      rfl

theorem cell22_2560092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2560092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560092 prefixEnd_2560092 := by exact prefixLift 2560092
  have htrace : WordTrace (prefixWord ++ tailWord_2560092) baseStart_2560092 baseEnd_2560092 := by
    simpa [prefixWord, tailWord_2560092, baseEnd_2560092] using wordTrace_append hprefix tailTrace_2560092
  have hstable : (prefixWord ++ tailWord_2560092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560092).length < 2 ^ (prefixWord ++ tailWord_2560092).sum := by decide
  have hdescent : baseEnd_2560092 < baseStart_2560092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560103 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2560103 : Nat := 118140960795 + 2560103 * 2 ^ 59
def prefixEnd_2560103 : Nat := 4983230072969 + 3 ^ 40 * 2560103 * 2
def baseEnd_2560103 : Nat := 876375576011668212625871

theorem tailTrace_2560103 : CollatzResearch.WordTrace tailWord_2560103 prefixEnd_2560103 876375576011668212625871 := by
  unfold tailWord_2560103
  simp only [CollatzResearch.WordTrace]
  refine ⟨93374627444191536627788963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62249751629461024418525975 93374627444191536627788963)
  ·
    refine ⟨140061941166287304941683445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93374627444191536627788963 140061941166287304941683445)
    ·
      refine ⟨13130806984339434838282823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140061941166287304941683445 13130806984339434838282823)
      ·
        refine ⟨19696210476509152257424235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13130806984339434838282823 19696210476509152257424235)
        ·
          refine ⟨29544315714763728386136353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19696210476509152257424235 29544315714763728386136353)
          ·
            refine ⟨22158236786072796289602265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29544315714763728386136353 22158236786072796289602265)
            ·
              refine ⟨16618677589554597217201699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22158236786072796289602265 16618677589554597217201699)
              ·
                refine ⟨24928016384331895825802549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16618677589554597217201699 24928016384331895825802549)
                ·
                  refine ⟨2337001536031115233668989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24928016384331895825802549 2337001536031115233668989)
                  ·
                    refine ⟨876375576011668212625871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337001536031115233668989 876375576011668212625871)
                    ·
                      rfl

theorem cell22_2560103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2560103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560103 prefixEnd_2560103 := by exact prefixLift 2560103
  have htrace : WordTrace (prefixWord ++ tailWord_2560103) baseStart_2560103 baseEnd_2560103 := by
    simpa [prefixWord, tailWord_2560103, baseEnd_2560103] using wordTrace_append hprefix tailTrace_2560103
  have hstable : (prefixWord ++ tailWord_2560103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560103).length < 2 ^ (prefixWord ++ tailWord_2560103).sum := by decide
  have hdescent : baseEnd_2560103 < baseStart_2560103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560120 : List Nat := [2, 1, 2, 1, 1, 1, 3, 7, 1, 3]
def baseStart_2560120 : Nat := 118140960795 + 2560120 * 2 ^ 59
def prefixEnd_2560120 : Nat := 4983230072969 + 3 ^ 40 * 2560120 * 2
def baseEnd_2560120 : Nat := 876381395459085834950819

theorem tailTrace_2560120 : CollatzResearch.WordTrace tailWord_2560120 prefixEnd_2560120 876381395459085834950819 := by
  unfold tailWord_2560120
  simp only [CollatzResearch.WordTrace]
  refine ⟨46687623742564974265578907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62250164990086632354105209 46687623742564974265578907)
  ·
    refine ⟨70031435613847461398368361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46687623742564974265578907 70031435613847461398368361)
    ·
      refine ⟨52523576710385596048776271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70031435613847461398368361 52523576710385596048776271)
      ·
        refine ⟨78785365065578394073164407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52523576710385596048776271 78785365065578394073164407)
        ·
          refine ⟨118178047598367591109746611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78785365065578394073164407 118178047598367591109746611)
          ·
            refine ⟨177267071397551386664619917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118178047598367591109746611 177267071397551386664619917)
            ·
              refine ⟨66475151774081769999232469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177267071397551386664619917 66475151774081769999232469)
              ·
                refine ⟨1558011369705041484357011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66475151774081769999232469 1558011369705041484357011)
                ·
                  refine ⟨2337017054557562226535517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558011369705041484357011 2337017054557562226535517)
                  ·
                    refine ⟨876381395459085834950819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337017054557562226535517 876381395459085834950819)
                    ·
                      rfl

theorem cell22_2560120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_2560120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560120 prefixEnd_2560120 := by exact prefixLift 2560120
  have htrace : WordTrace (prefixWord ++ tailWord_2560120) baseStart_2560120 baseEnd_2560120 := by
    simpa [prefixWord, tailWord_2560120, baseEnd_2560120] using wordTrace_append hprefix tailTrace_2560120
  have hstable : (prefixWord ++ tailWord_2560120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560120).length < 2 ^ (prefixWord ++ tailWord_2560120).sum := by decide
  have hdescent : baseEnd_2560120 < baseStart_2560120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560133 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 5]
def baseStart_2560133 : Nat := 118140960795 + 2560133 * 2 ^ 59
def prefixEnd_2560133 : Nat := 4983230072969 + 3 ^ 40 * 2560133 * 2
def baseEnd_2560133 : Nat := 292128615208252711458593

theorem tailTrace_2560133 : CollatzResearch.WordTrace tailWord_2560133 prefixEnd_2560133 292128615208252711458593 := by
  unfold tailWord_2560133
  simp only [CollatzResearch.WordTrace]
  refine ⟨93375721634082851751381053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62250481089388567834254035 93375721634082851751381053)
  ·
    refine ⟨35015895612781069406767895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93375721634082851751381053 35015895612781069406767895)
    ·
      refine ⟨52523843419171604110151843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35015895612781069406767895 52523843419171604110151843)
      ·
        refine ⟨78785765128757406165227765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52523843419171604110151843 78785765128757406165227765)
        ·
          refine ⟨7386165480821006827990103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78785765128757406165227765 7386165480821006827990103)
          ·
            refine ⟨11079248221231510241985155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7386165480821006827990103 11079248221231510241985155)
            ·
              refine ⟨16618872331847265362977733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11079248221231510241985155 16618872331847265362977733)
              ·
                refine ⟨3116038562221362255558325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16618872331847265362977733 3116038562221362255558325)
                ·
                  refine ⟨292128615208252711458593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3116038562221362255558325 292128615208252711458593)
                  ·
                    rfl

theorem cell22_2560133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_2560133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560133 prefixEnd_2560133 := by exact prefixLift 2560133
  have htrace : WordTrace (prefixWord ++ tailWord_2560133) baseStart_2560133 baseEnd_2560133 := by
    simpa [prefixWord, tailWord_2560133, baseEnd_2560133] using wordTrace_append hprefix tailTrace_2560133
  have hstable : (prefixWord ++ tailWord_2560133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560133).length < 2 ^ (prefixWord ++ tailWord_2560133).sum := by decide
  have hdescent : baseEnd_2560133 < baseStart_2560133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560210 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2560210 : Nat := 118140960795 + 2560210 * 2 ^ 59
def prefixEnd_2560210 : Nat := 4983230072969 + 3 ^ 40 * 2560210 * 2
def baseEnd_2560210 : Nat := 876412204298355600200543

theorem tailTrace_2560210 : CollatzResearch.WordTrace tailWord_2560210 prefixEnd_2560210 876412204298355600200543 := by
  unfold tailWord_2560210
  simp only [CollatzResearch.WordTrace]
  refine ⟨23344632513700973475483521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62252353369869262601289389 23344632513700973475483521)
  ·
    refine ⟨17508474385275730106612641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23344632513700973475483521 17508474385275730106612641)
    ·
      refine ⟨13131355788956797579959481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17508474385275730106612641 13131355788956797579959481)
      ·
        refine ⟨9848516841717598184969611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13131355788956797579959481 9848516841717598184969611)
        ·
          refine ⟨14772775262576397277454417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9848516841717598184969611 14772775262576397277454417)
          ·
            refine ⟨11079581446932297958090813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14772775262576397277454417 11079581446932297958090813)
            ·
              refine ⟨4154843042599611734284055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11079581446932297958090813 4154843042599611734284055)
              ·
                refine ⟨6232264563899417601426083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154843042599611734284055 6232264563899417601426083)
                ·
                  refine ⟨9348396845849126402139125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232264563899417601426083 9348396845849126402139125)
                  ·
                    refine ⟨876412204298355600200543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9348396845849126402139125 876412204298355600200543)
                    ·
                      rfl

theorem cell22_2560210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2560210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560210 prefixEnd_2560210 := by exact prefixLift 2560210
  have htrace : WordTrace (prefixWord ++ tailWord_2560210) baseStart_2560210 baseEnd_2560210 := by
    simpa [prefixWord, tailWord_2560210, baseEnd_2560210] using wordTrace_append hprefix tailTrace_2560210
  have hstable : (prefixWord ++ tailWord_2560210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560210).length < 2 ^ (prefixWord ++ tailWord_2560210).sum := by decide
  have hdescent : baseEnd_2560210 < baseStart_2560210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560214 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2560214 : Nat := 118140960795 + 2560214 * 2 ^ 59
def prefixEnd_2560214 : Nat := 4983230072969 + 3 ^ 40 * 2560214 * 2
def baseEnd_2560214 : Nat := 876413573580100923100531

theorem tailTrace_2560214 : CollatzResearch.WordTrace tailWord_2560214 prefixEnd_2560214 876413573580100923100531 := by
  unfold tailWord_2560214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5836167246674337661567481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62252450631192935056719797 5836167246674337661567481)
  ·
    refine ⟨4377125435005753246175611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5836167246674337661567481 4377125435005753246175611)
    ·
      refine ⟨6565688152508629869263417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377125435005753246175611 6565688152508629869263417)
      ·
        refine ⟨4924266114381472401947563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6565688152508629869263417 4924266114381472401947563)
        ·
          refine ⟨7386399171572208602921345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924266114381472401947563 7386399171572208602921345)
          ·
            refine ⟨5539799378679156452191009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7386399171572208602921345 5539799378679156452191009)
            ·
              refine ⟨4154849534009367339143257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539799378679156452191009 4154849534009367339143257)
              ·
                refine ⟨3116137150507025504357443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4154849534009367339143257 3116137150507025504357443)
                ·
                  refine ⟨4674205725760538256536165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116137150507025504357443 4674205725760538256536165)
                  ·
                    refine ⟨876413573580100923100531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4674205725760538256536165 876413573580100923100531)
                    ·
                      rfl

theorem cell22_2560214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2560214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560214 prefixEnd_2560214 := by exact prefixLift 2560214
  have htrace : WordTrace (prefixWord ++ tailWord_2560214) baseStart_2560214 baseEnd_2560214 := by
    simpa [prefixWord, tailWord_2560214, baseEnd_2560214] using wordTrace_append hprefix tailTrace_2560214
  have hstable : (prefixWord ++ tailWord_2560214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560214).length < 2 ^ (prefixWord ++ tailWord_2560214).sum := by decide
  have hdescent : baseEnd_2560214 < baseStart_2560214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560345 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 4, 3]
def baseStart_2560345 : Nat := 118140960795 + 2560345 * 2 ^ 59
def prefixEnd_2560345 : Nat := 4983230072969 + 3 ^ 40 * 2560345 * 2
def baseEnd_2560345 : Nat := 876458417557260248075129

theorem tailTrace_2560345 : CollatzResearch.WordTrace tailWord_2560345 prefixEnd_2560345 876458417557260248075129 := by
  unfold tailWord_2560345
  simp only [CollatzResearch.WordTrace]
  refine ⟨93383453909314811958098489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62255635939543207972065659 93383453909314811958098489)
  ·
    refine ⟨70037590431986108968573867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93383453909314811958098489 70037590431986108968573867)
    ·
      refine ⟨105056385647979163452860801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70037590431986108968573867 105056385647979163452860801)
      ·
        refine ⟨78792289235984372589645601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105056385647979163452860801 78792289235984372589645601)
        ·
          refine ⟨59094216926988279442234201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78792289235984372589645601 59094216926988279442234201)
          ·
            refine ⟨44320662695241209581675651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59094216926988279442234201 44320662695241209581675651)
            ·
              refine ⟨66480994042861814372513477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44320662695241209581675651 66480994042861814372513477)
              ·
                refine ⟨12465186383036590194846277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66480994042861814372513477 12465186383036590194846277)
                ·
                  refine ⟨2337222446819360661533677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12465186383036590194846277 2337222446819360661533677)
                  ·
                    refine ⟨876458417557260248075129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337222446819360661533677 876458417557260248075129)
                    ·
                      rfl

theorem cell22_2560345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_2560345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560345 prefixEnd_2560345 := by exact prefixLift 2560345
  have htrace : WordTrace (prefixWord ++ tailWord_2560345) baseStart_2560345 baseEnd_2560345 := by
    simpa [prefixWord, tailWord_2560345, baseEnd_2560345] using wordTrace_append hprefix tailTrace_2560345
  have hstable : (prefixWord ++ tailWord_2560345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560345).length < 2 ^ (prefixWord ++ tailWord_2560345).sum := by decide
  have hdescent : baseEnd_2560345 < baseStart_2560345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560379 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 2, 3]
def baseStart_2560379 : Nat := 118140960795 + 2560379 * 2 ^ 59
def prefixEnd_2560379 : Nat := 4983230072969 + 3 ^ 40 * 2560379 * 2
def baseEnd_2560379 : Nat := 876470056452095492725025

theorem tailTrace_2560379 : CollatzResearch.WordTrace tailWord_2560379 prefixEnd_2560379 876470056452095492725025 := by
  unfold tailWord_2560379
  simp only [CollatzResearch.WordTrace]
  refine ⟨93384693991191635764836191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62256462660794423843224127 93384693991191635764836191)
  ·
    refine ⟨140077040986787453647254287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93384693991191635764836191 140077040986787453647254287)
    ·
      refine ⟨210115561480181180470881431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140077040986787453647254287 210115561480181180470881431)
      ·
        refine ⟨315173342220271770706322147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210115561480181180470881431 315173342220271770706322147)
        ·
          refine ⟨472760013330407656059483221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315173342220271770706322147 472760013330407656059483221)
          ·
            refine ⟨5540156406215714719447069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 472760013330407656059483221 5540156406215714719447069)
            ·
              refine ⟨2077558652330893019792651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5540156406215714719447069 2077558652330893019792651)
              ·
                refine ⟨3116337978496339529688977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077558652330893019792651 3116337978496339529688977)
                ·
                  refine ⟨2337253483872254647266733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3116337978496339529688977 2337253483872254647266733)
                  ·
                    refine ⟨876470056452095492725025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337253483872254647266733 876470056452095492725025)
                    ·
                      rfl

theorem cell22_2560379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 3].length) (baseStart_2560379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560379 prefixEnd_2560379 := by exact prefixLift 2560379
  have htrace : WordTrace (prefixWord ++ tailWord_2560379) baseStart_2560379 baseEnd_2560379 := by
    simpa [prefixWord, tailWord_2560379, baseEnd_2560379] using wordTrace_append hprefix tailTrace_2560379
  have hstable : (prefixWord ++ tailWord_2560379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560379).length < 2 ^ (prefixWord ++ tailWord_2560379).sum := by decide
  have hdescent : baseEnd_2560379 < baseStart_2560379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560420 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 7]
def baseStart_2560420 : Nat := 118140960795 + 2560420 * 2 ^ 59
def prefixEnd_2560420 : Nat := 4983230072969 + 3 ^ 40 * 2560420 * 2
def baseEnd_2560420 : Nat := 292161363863328350816633

theorem tailTrace_2560420 : CollatzResearch.WordTrace tailWord_2560420 prefixEnd_2560420 292161363863328350816633 := by
  unfold tailWord_2560420
  simp only [CollatzResearch.WordTrace]
  refine ⟨46693094692021549883539357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62257459589362066511385809 46693094692021549883539357)
  ·
    refine ⟨17509910509508081206327259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46693094692021549883539357 17509910509508081206327259)
    ·
      refine ⟨26264865764262121809490889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17509910509508081206327259 26264865764262121809490889)
      ·
        refine ⟨19698649323196591357118167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26264865764262121809490889 19698649323196591357118167)
        ·
          refine ⟨29547973984794887035677251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19698649323196591357118167 29547973984794887035677251)
          ·
            refine ⟨44321960977192330553515877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29547973984794887035677251 44321960977192330553515877)
            ·
              refine ⟨8310367683223561978784227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44321960977192330553515877 8310367683223561978784227)
              ·
                refine ⟨12465551524835342968176341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8310367683223561978784227 12465551524835342968176341)
                ·
                  refine ⟨292161363863328350816633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12465551524835342968176341 292161363863328350816633)
                  ·
                    rfl

theorem cell22_2560420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_2560420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560420 prefixEnd_2560420 := by exact prefixLift 2560420
  have htrace : WordTrace (prefixWord ++ tailWord_2560420) baseStart_2560420 baseEnd_2560420 := by
    simpa [prefixWord, tailWord_2560420, baseEnd_2560420] using wordTrace_append hprefix tailTrace_2560420
  have hstable : (prefixWord ++ tailWord_2560420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560420).length < 2 ^ (prefixWord ++ tailWord_2560420).sum := by decide
  have hdescent : baseEnd_2560420 < baseStart_2560420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560426 : List Nat := [3, 1, 6, 1, 1, 1, 2, 7]
def baseStart_2560426 : Nat := 118140960795 + 2560426 * 2 ^ 59
def prefixEnd_2560426 : Nat := 4983230072969 + 3 ^ 40 * 2560426 * 2
def baseEnd_2560426 : Nat := 97387349501400337422209

theorem tailTrace_2560426 : CollatzResearch.WordTrace tailWord_2560426 prefixEnd_2560426 97387349501400337422209 := by
  unfold tailWord_2560426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23346602055505340697949283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62257605481347575194531421 23346602055505340697949283)
  ·
    refine ⟨35019903083258011046923925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23346602055505340697949283 35019903083258011046923925)
    ·
      refine ⟨1641557957027719267824559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35019903083258011046923925 1641557957027719267824559)
      ·
        refine ⟨2462336935541578901736839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641557957027719267824559 2462336935541578901736839)
        ·
          refine ⟨3693505403312368352605259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462336935541578901736839 3693505403312368352605259)
          ·
            refine ⟨5540258104968552528907889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693505403312368352605259 5540258104968552528907889)
            ·
              refine ⟨4155193578726414396680917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540258104968552528907889 4155193578726414396680917)
              ·
                refine ⟨97387349501400337422209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4155193578726414396680917 97387349501400337422209)
                ·
                  rfl

theorem cell22_2560426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_2560426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560426 prefixEnd_2560426 := by exact prefixLift 2560426
  have htrace : WordTrace (prefixWord ++ tailWord_2560426) baseStart_2560426 baseEnd_2560426 := by
    simpa [prefixWord, tailWord_2560426, baseEnd_2560426] using wordTrace_append hprefix tailTrace_2560426
  have hstable : (prefixWord ++ tailWord_2560426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560426).length < 2 ^ (prefixWord ++ tailWord_2560426).sum := by decide
  have hdescent : baseEnd_2560426 < baseStart_2560426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560480 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_2560480 : Nat := 118140960795 + 2560480 * 2 ^ 59
def prefixEnd_2560480 : Nat := 4983230072969 + 3 ^ 40 * 2560480 * 2
def baseEnd_2560480 : Nat := 876504630816164895949715

theorem tailTrace_2560480 : CollatzResearch.WordTrace tailWord_2560480 prefixEnd_2560480 876504630816164895949715 := by
  unfold tailWord_2560480
  simp only [CollatzResearch.WordTrace]
  refine ⟨46694188881912865007131447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62258918509217153342841929 46694188881912865007131447)
  ·
    refine ⟨70041283322869297510697171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46694188881912865007131447 70041283322869297510697171)
    ·
      refine ⟨105061924984303946266045757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70041283322869297510697171 105061924984303946266045757)
      ·
        refine ⟨39398221869113979849767159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105061924984303946266045757 39398221869113979849767159)
        ·
          refine ⟨59097332803670969774650739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39398221869113979849767159 59097332803670969774650739)
          ·
            refine ⟨88645999205506454661976109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59097332803670969774650739 88645999205506454661976109)
            ·
              refine ⟨33242249702064920498241041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88645999205506454661976109 33242249702064920498241041)
              ·
                refine ⟨24931687276548690373680781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33242249702064920498241041 24931687276548690373680781)
                ·
                  refine ⟨9349382728705758890130293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24931687276548690373680781 9349382728705758890130293)
                  ·
                    refine ⟨876504630816164895949715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9349382728705758890130293 876504630816164895949715)
                    ·
                      rfl

theorem cell22_2560480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_2560480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560480 prefixEnd_2560480 := by exact prefixLift 2560480
  have htrace : WordTrace (prefixWord ++ tailWord_2560480) baseStart_2560480 baseEnd_2560480 := by
    simpa [prefixWord, tailWord_2560480, baseEnd_2560480] using wordTrace_append hprefix tailTrace_2560480
  have hstable : (prefixWord ++ tailWord_2560480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560480).length < 2 ^ (prefixWord ++ tailWord_2560480).sum := by decide
  have hdescent : baseEnd_2560480 < baseStart_2560480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560495 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 1, 6]
def baseStart_2560495 : Nat := 118140960795 + 2560495 * 2 ^ 59
def prefixEnd_2560495 : Nat := 4983230072969 + 3 ^ 40 * 2560495 * 2
def baseEnd_2560495 : Nat := 876509765622709856824669

theorem tailTrace_2560495 : CollatzResearch.WordTrace tailWord_2560495 prefixEnd_2560495 876509765622709856824669 := by
  unfold tailWord_2560495
  simp only [CollatzResearch.WordTrace]
  refine ⟨93388924858771387576058939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62259283239180925050705959 93388924858771387576058939)
  ·
    refine ⟨140083387288157081364088409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93388924858771387576058939 140083387288157081364088409)
    ·
      refine ⟨105062540466117811023066307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140083387288157081364088409 105062540466117811023066307)
      ·
        refine ⟨157593810699176716534599461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105062540466117811023066307 157593810699176716534599461)
        ·
          refine ⟨29548839506095634350237399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157593810699176716534599461 29548839506095634350237399)
          ·
            refine ⟨44323259259143451525356099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29548839506095634350237399 44323259259143451525356099)
            ·
              refine ⟨66484888888715177288034149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44323259259143451525356099 66484888888715177288034149)
              ·
                refine ⟨12465916666634095741506403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66484888888715177288034149 12465916666634095741506403)
                ·
                  refine ⟨18698874999951143612259605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12465916666634095741506403 18698874999951143612259605)
                  ·
                    refine ⟨876509765622709856824669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18698874999951143612259605 876509765622709856824669)
                    ·
                      rfl

theorem cell22_2560495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_2560495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560495 prefixEnd_2560495 := by exact prefixLift 2560495
  have htrace : WordTrace (prefixWord ++ tailWord_2560495) baseStart_2560495 baseEnd_2560495 := by
    simpa [prefixWord, tailWord_2560495, baseEnd_2560495] using wordTrace_append hprefix tailTrace_2560495
  have hstable : (prefixWord ++ tailWord_2560495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560495).length < 2 ^ (prefixWord ++ tailWord_2560495).sum := by decide
  have hdescent : baseEnd_2560495 < baseStart_2560495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560497 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2560497 : Nat := 118140960795 + 2560497 * 2 ^ 59
def prefixEnd_2560497 : Nat := 4983230072969 + 3 ^ 40 * 2560497 * 2
def baseEnd_2560497 : Nat := 876510450263582518274663

theorem tailTrace_2560497 : CollatzResearch.WordTrace tailWord_2560497 prefixEnd_2560497 876510450263582518274663 := by
  unfold tailWord_2560497
  simp only [CollatzResearch.WordTrace]
  refine ⟨93388997804764141917631745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62259331869842761278421163 93388997804764141917631745)
  ·
    refine ⟨70041748353573106438223809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93388997804764141917631745 70041748353573106438223809)
    ·
      refine ⟨52531311265179829828667857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70041748353573106438223809 52531311265179829828667857)
      ·
        refine ⟨39398483448884872371500893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52531311265179829828667857 39398483448884872371500893)
        ·
          refine ⟨14774431293331827139312835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39398483448884872371500893 14774431293331827139312835)
          ·
            refine ⟨22161646939997740708969253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14774431293331827139312835 22161646939997740708969253)
            ·
              refine ⟨4155308801249576382931735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22161646939997740708969253 4155308801249576382931735)
              ·
                refine ⟨6232963201874364574397603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155308801249576382931735 6232963201874364574397603)
                ·
                  refine ⟨9349444802811546861596405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232963201874364574397603 9349444802811546861596405)
                  ·
                    refine ⟨876510450263582518274663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9349444802811546861596405 876510450263582518274663)
                    ·
                      rfl

theorem cell22_2560497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2560497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560497 prefixEnd_2560497 := by exact prefixLift 2560497
  have htrace : WordTrace (prefixWord ++ tailWord_2560497) baseStart_2560497 baseEnd_2560497 := by
    simpa [prefixWord, tailWord_2560497, baseEnd_2560497] using wordTrace_append hprefix tailTrace_2560497
  have hstable : (prefixWord ++ tailWord_2560497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560497).length < 2 ^ (prefixWord ++ tailWord_2560497).sum := by decide
  have hdescent : baseEnd_2560497 < baseStart_2560497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560516 : List Nat := [2, 3, 2, 3, 1, 2, 2, 3, 4]
def baseStart_2560516 : Nat := 118140960795 + 2560516 * 2 ^ 59
def prefixEnd_2560516 : Nat := 4983230072969 + 3 ^ 40 * 2560516 * 2
def baseEnd_2560516 : Nat := 292172318117290934016535

theorem tailTrace_2560516 : CollatzResearch.WordTrace tailWord_2560516 prefixEnd_2560516 292172318117290934016535 := by
  unfold tailWord_2560516
  simp only [CollatzResearch.WordTrace]
  refine ⟨46694845395847654081286701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62259793861130205441715601 46694845395847654081286701)
  ·
    refine ⟨17510567023442870280482513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46694845395847654081286701 17510567023442870280482513)
    ·
      refine ⟨13132925267582152710361885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17510567023442870280482513 13132925267582152710361885)
      ·
        refine ⟨4924846975343307266385707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13132925267582152710361885 4924846975343307266385707)
        ·
          refine ⟨7387270463014960899578561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924846975343307266385707 7387270463014960899578561)
          ·
            refine ⟨5540452847261220674683921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7387270463014960899578561 5540452847261220674683921)
            ·
              refine ⟨4155339635445915506012941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540452847261220674683921 4155339635445915506012941)
              ·
                refine ⟨1558252363292218314754853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4155339635445915506012941 1558252363292218314754853)
                ·
                  refine ⟨292172318117290934016535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1558252363292218314754853 292172318117290934016535)
                  ·
                    rfl

theorem cell22_2560516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_2560516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560516 prefixEnd_2560516 := by exact prefixLift 2560516
  have htrace : WordTrace (prefixWord ++ tailWord_2560516) baseStart_2560516 baseEnd_2560516 := by
    simpa [prefixWord, tailWord_2560516, baseEnd_2560516] using wordTrace_append hprefix tailTrace_2560516
  have hstable : (prefixWord ++ tailWord_2560516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560516).length < 2 ^ (prefixWord ++ tailWord_2560516).sum := by decide
  have hdescent : baseEnd_2560516 < baseStart_2560516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560548 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_2560548 : Nat := 118140960795 + 2560548 * 2 ^ 59
def prefixEnd_2560548 : Nat := 4983230072969 + 3 ^ 40 * 2560548 * 2
def baseEnd_2560548 : Nat := 876527908605835385249507

theorem tailTrace_2560548 : CollatzResearch.WordTrace tailWord_2560548 prefixEnd_2560548 876527908605835385249507 := by
  unfold tailWord_2560548
  simp only [CollatzResearch.WordTrace]
  refine ⟨46695428963789688813869149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62260571951719585085158865 46695428963789688813869149)
  ·
    refine ⟨17510785861421133305200931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46695428963789688813869149 17510785861421133305200931)
    ·
      refine ⟨26266178792131699957801397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17510785861421133305200931 26266178792131699957801397)
      ·
        refine ⟨2462454261762346871043881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26266178792131699957801397 2462454261762346871043881)
        ·
          refine ⟨1846840696321760153282911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462454261762346871043881 1846840696321760153282911)
          ·
            refine ⟨2770261044482640229924367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846840696321760153282911 2770261044482640229924367)
            ·
              refine ⟨4155391566723960344886551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770261044482640229924367 4155391566723960344886551)
              ·
                refine ⟨6233087350085940517329827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155391566723960344886551 6233087350085940517329827)
                ·
                  refine ⟨9349631025128910775994741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233087350085940517329827 9349631025128910775994741)
                  ·
                    refine ⟨876527908605835385249507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9349631025128910775994741 876527908605835385249507)
                    ·
                      rfl

theorem cell22_2560548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_2560548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560548 prefixEnd_2560548 := by exact prefixLift 2560548
  have htrace : WordTrace (prefixWord ++ tailWord_2560548) baseStart_2560548 baseEnd_2560548 := by
    simpa [prefixWord, tailWord_2560548, baseEnd_2560548] using wordTrace_append hprefix tailTrace_2560548
  have hstable : (prefixWord ++ tailWord_2560548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560548).length < 2 ^ (prefixWord ++ tailWord_2560548).sum := by decide
  have hdescent : baseEnd_2560548 < baseStart_2560548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560572 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 7]
def baseStart_2560572 : Nat := 118140960795 + 2560572 * 2 ^ 59
def prefixEnd_2560572 : Nat := 4983230072969 + 3 ^ 40 * 2560572 * 2
def baseEnd_2560572 : Nat := 292178708098769107549811

theorem tailTrace_2560572 : CollatzResearch.WordTrace tailWord_2560572 prefixEnd_2560572 292178708098769107549811 := by
  unfold tailWord_2560572
  simp only [CollatzResearch.WordTrace]
  refine ⟨46695866639746214863305985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62261155519661619817741313 46695866639746214863305985)
  ·
    refine ⟨35021899979809661147479489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46695866639746214863305985 35021899979809661147479489)
    ·
      refine ⟨26266424984857245860609617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35021899979809661147479489 26266424984857245860609617)
      ·
        refine ⟨19699818738642934395457213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26266424984857245860609617 19699818738642934395457213)
        ·
          refine ⟨7387432026991100398296455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19699818738642934395457213 7387432026991100398296455)
          ·
            refine ⟨11081148040486650597444683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7387432026991100398296455 11081148040486650597444683)
            ·
              refine ⟨16621722060729975896167025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11081148040486650597444683 16621722060729975896167025)
              ·
                refine ⟨12466291545547481922125269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16621722060729975896167025 12466291545547481922125269)
                ·
                  refine ⟨292178708098769107549811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12466291545547481922125269 292178708098769107549811)
                  ·
                    rfl

theorem cell22_2560572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_2560572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560572 prefixEnd_2560572 := by exact prefixLift 2560572
  have htrace : WordTrace (prefixWord ++ tailWord_2560572) baseStart_2560572 baseEnd_2560572 := by
    simpa [prefixWord, tailWord_2560572, baseEnd_2560572] using wordTrace_append hprefix tailTrace_2560572
  have hstable : (prefixWord ++ tailWord_2560572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560572).length < 2 ^ (prefixWord ++ tailWord_2560572).sum := by decide
  have hdescent : baseEnd_2560572 < baseStart_2560572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560576 : List Nat := [2, 1, 1, 2, 2, 2, 5, 3, 1, 3]
def baseStart_2560576 : Nat := 118140960795 + 2560576 * 2 ^ 59
def prefixEnd_2560576 : Nat := 4983230072969 + 3 ^ 40 * 2560576 * 2
def baseEnd_2560576 : Nat := 876537493578052645549421

theorem tailTrace_2560576 : CollatzResearch.WordTrace tailWord_2560576 prefixEnd_2560576 876537493578052645549421 := by
  unfold tailWord_2560576
  simp only [CollatzResearch.WordTrace]
  refine ⟨46695939585738969204878791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62261252780985292273171721 46695939585738969204878791)
  ·
    refine ⟨70043909378608453807318187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46695939585738969204878791 70043909378608453807318187)
    ·
      refine ⟨105065864067912680710977281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70043909378608453807318187 105065864067912680710977281)
      ·
        refine ⟨78799398050934510533232961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105065864067912680710977281 78799398050934510533232961)
        ·
          refine ⟨59099548538200882899924721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78799398050934510533232961 59099548538200882899924721)
          ·
            refine ⟨44324661403650662174943541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59099548538200882899924721 44324661403650662174943541)
            ·
              refine ⟨4155437006592249578900957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44324661403650662174943541 4155437006592249578900957)
              ·
                refine ⟨1558288877472093592087859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4155437006592249578900957 1558288877472093592087859)
                ·
                  refine ⟨2337433316208140388131789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558288877472093592087859 2337433316208140388131789)
                  ·
                    refine ⟨876537493578052645549421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337433316208140388131789 876537493578052645549421)
                    ·
                      rfl

theorem cell22_2560576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 3].length) (baseStart_2560576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560576 prefixEnd_2560576 := by exact prefixLift 2560576
  have htrace : WordTrace (prefixWord ++ tailWord_2560576) baseStart_2560576 baseEnd_2560576 := by
    simpa [prefixWord, tailWord_2560576, baseEnd_2560576] using wordTrace_append hprefix tailTrace_2560576
  have hstable : (prefixWord ++ tailWord_2560576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560576).length < 2 ^ (prefixWord ++ tailWord_2560576).sum := by decide
  have hdescent : baseEnd_2560576 < baseStart_2560576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560589 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2560589 : Nat := 118140960795 + 2560589 * 2 ^ 59
def prefixEnd_2560589 : Nat := 4983230072969 + 3 ^ 40 * 2560589 * 2
def baseEnd_2560589 : Nat := 292180647914574981658127

theorem tailTrace_2560589 : CollatzResearch.WordTrace tailWord_2560589 prefixEnd_2560589 292180647914574981658127 := by
  unfold tailWord_2560589
  simp only [CollatzResearch.WordTrace]
  refine ⟨93392353320430841629980821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62261568880287227753320547 93392353320430841629980821)
  ·
    refine ⟨4377766561895195701405351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93392353320430841629980821 4377766561895195701405351)
    ·
      refine ⟨6566649842842793552108027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377766561895195701405351 6566649842842793552108027)
      ·
        refine ⟨9849974764264190328162041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6566649842842793552108027 9849974764264190328162041)
        ·
          refine ⟨7387481073198142746121531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9849974764264190328162041 7387481073198142746121531)
          ·
            refine ⟨11081221609797214119182297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7387481073198142746121531 11081221609797214119182297)
            ·
              refine ⟨8310916207347910589386723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11081221609797214119182297 8310916207347910589386723)
              ·
                refine ⟨12466374311021865884080085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8310916207347910589386723 12466374311021865884080085)
                ·
                  refine ⟨292180647914574981658127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12466374311021865884080085 292180647914574981658127)
                  ·
                    rfl

theorem cell22_2560589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2560589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560589 prefixEnd_2560589 := by exact prefixLift 2560589
  have htrace : WordTrace (prefixWord ++ tailWord_2560589) baseStart_2560589 baseEnd_2560589 := by
    simpa [prefixWord, tailWord_2560589, baseEnd_2560589] using wordTrace_append hprefix tailTrace_2560589
  have hstable : (prefixWord ++ tailWord_2560589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560589).length < 2 ^ (prefixWord ++ tailWord_2560589).sum := by decide
  have hdescent : baseEnd_2560589 < baseStart_2560589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560593 : List Nat := [1, 2, 2, 1, 3, 4, 3, 2, 1, 3]
def baseStart_2560593 : Nat := 118140960795 + 2560593 * 2 ^ 59
def prefixEnd_2560593 : Nat := 4983230072969 + 3 ^ 40 * 2560593 * 2
def baseEnd_2560593 : Nat := 876543313025470267874369

theorem tailTrace_2560593 : CollatzResearch.WordTrace tailWord_2560593 prefixEnd_2560593 876543313025470267874369 := by
  unfold tailWord_2560593
  simp only [CollatzResearch.WordTrace]
  refine ⟨93392499212416350313126433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62261666141610900208750955 93392499212416350313126433)
  ·
    refine ⟨70044374409312262734844825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93392499212416350313126433 70044374409312262734844825)
    ·
      refine ⟨52533280806984197051133619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70044374409312262734844825 52533280806984197051133619)
      ·
        refine ⟨78799921210476295576700429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52533280806984197051133619 78799921210476295576700429)
        ·
          refine ⟨29549970453928610841262661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78799921210476295576700429 29549970453928610841262661)
          ·
            refine ⟨5540619460111614532736749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29549970453928610841262661 5540619460111614532736749)
            ·
              refine ⟨2077732297541855449776281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5540619460111614532736749 2077732297541855449776281)
              ·
                refine ⟨1558299223156391587332211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077732297541855449776281 1558299223156391587332211)
                ·
                  refine ⟨2337448834734587380998317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558299223156391587332211 2337448834734587380998317)
                  ·
                    refine ⟨876543313025470267874369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337448834734587380998317 876543313025470267874369)
                    ·
                      rfl

theorem cell22_2560593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_2560593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560593 prefixEnd_2560593 := by exact prefixLift 2560593
  have htrace : WordTrace (prefixWord ++ tailWord_2560593) baseStart_2560593 baseEnd_2560593 := by
    simpa [prefixWord, tailWord_2560593, baseEnd_2560593] using wordTrace_append hprefix tailTrace_2560593
  have hstable : (prefixWord ++ tailWord_2560593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560593).length < 2 ^ (prefixWord ++ tailWord_2560593).sum := by decide
  have hdescent : baseEnd_2560593 < baseStart_2560593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560632 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_2560632 : Nat := 118140960795 + 2560632 * 2 ^ 59
def prefixEnd_2560632 : Nat := 4983230072969 + 3 ^ 40 * 2560632 * 2
def baseEnd_2560632 : Nat := 876556663522487166149249

theorem tailTrace_2560632 : CollatzResearch.WordTrace tailWord_2560632 prefixEnd_2560632 876556663522487166149249 := by
  unfold tailWord_2560632
  simp only [CollatzResearch.WordTrace]
  refine ⟨46696960829637529986898075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62262614439516706649197433 46696960829637529986898075)
  ·
    refine ⟨70045441244456294980347113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46696960829637529986898075 70045441244456294980347113)
    ·
      refine ⟨52534080933342221235260335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70045441244456294980347113 52534080933342221235260335)
      ·
        refine ⟨78801121400013331852890503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52534080933342221235260335 78801121400013331852890503)
        ·
          refine ⟨118201682100019997779335755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78801121400013331852890503 118201682100019997779335755)
          ·
            refine ⟨177302523150029996669003633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118201682100019997779335755 177302523150029996669003633)
            ·
              refine ⟨132976892362522497501752725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177302523150029996669003633 132976892362522497501752725)
              ·
                refine ⟨6233291829493242070394659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132976892362522497501752725 6233291829493242070394659)
                ·
                  refine ⟨9349937744239863105591989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233291829493242070394659 9349937744239863105591989)
                  ·
                    refine ⟨876556663522487166149249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9349937744239863105591989 876556663522487166149249)
                    ·
                      rfl

theorem cell22_2560632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_2560632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560632 prefixEnd_2560632 := by exact prefixLift 2560632
  have htrace : WordTrace (prefixWord ++ tailWord_2560632) baseStart_2560632 baseEnd_2560632 := by
    simpa [prefixWord, tailWord_2560632, baseEnd_2560632] using wordTrace_append hprefix tailTrace_2560632
  have hstable : (prefixWord ++ tailWord_2560632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560632).length < 2 ^ (prefixWord ++ tailWord_2560632).sum := by decide
  have hdescent : baseEnd_2560632 < baseStart_2560632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560717 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2560717 : Nat := 118140960795 + 2560717 * 2 ^ 59
def prefixEnd_2560717 : Nat := 4983230072969 + 3 ^ 40 * 2560717 * 2
def baseEnd_2560717 : Nat := 876585760759575277773989

theorem tailTrace_2560717 : CollatzResearch.WordTrace tailWord_2560717 prefixEnd_2560717 876585760759575277773989 := by
  unfold tailWord_2560717
  simp only [CollatzResearch.WordTrace]
  refine ⟨93397021863967119490640405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62264681242644746327093603 93397021863967119490640405)
  ·
    refine ⟨4377985399873458726123769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93397021863967119490640405 4377985399873458726123769)
    ·
      refine ⟨3283489049905094044592827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4377985399873458726123769 3283489049905094044592827)
      ·
        refine ⟨4925233574857641066889241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3283489049905094044592827 4925233574857641066889241)
        ·
          refine ⟨3693925181143230800166931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4925233574857641066889241 3693925181143230800166931)
          ·
            refine ⟨5540887771714846200250397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693925181143230800166931 5540887771714846200250397)
            ·
              refine ⟨2077832914393067325093899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5540887771714846200250397 2077832914393067325093899)
              ·
                refine ⟨3116749371589600987640849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077832914393067325093899 3116749371589600987640849)
                ·
                  refine ⟨2337562028692200740730637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3116749371589600987640849 2337562028692200740730637)
                  ·
                    refine ⟨876585760759575277773989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337562028692200740730637 876585760759575277773989)
                    ·
                      rfl

theorem cell22_2560717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2560717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560717 prefixEnd_2560717 := by exact prefixLift 2560717
  have htrace : WordTrace (prefixWord ++ tailWord_2560717) baseStart_2560717 baseEnd_2560717 := by
    simpa [prefixWord, tailWord_2560717, baseEnd_2560717] using wordTrace_append hprefix tailTrace_2560717
  have hstable : (prefixWord ++ tailWord_2560717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560717).length < 2 ^ (prefixWord ++ tailWord_2560717).sum := by decide
  have hdescent : baseEnd_2560717 < baseStart_2560717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560818 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_2560818 : Nat := 118140960795 + 2560818 * 2 ^ 59
def prefixEnd_2560818 : Nat := 4983230072969 + 3 ^ 40 * 2560818 * 2
def baseEnd_2560818 : Nat := 876620335123644680998679

theorem tailTrace_2560818 : CollatzResearch.WordTrace tailWord_2560818 prefixEnd_2560818 876620335123644680998679 := by
  unfold tailWord_2560818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23350176409150303435016777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62267137091067475826711405 23350176409150303435016777)
  ·
    refine ⟨17512632306862727576262583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23350176409150303435016777 17512632306862727576262583)
    ·
      refine ⟨26268948460294091364393875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17512632306862727576262583 26268948460294091364393875)
      ·
        refine ⟨39403422690441137046590813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26268948460294091364393875 39403422690441137046590813)
        ·
          refine ⟨14776283508915426392471555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39403422690441137046590813 14776283508915426392471555)
          ·
            refine ⟨22164425263373139588707333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14776283508915426392471555 22164425263373139588707333)
            ·
              refine ⟨4155829736882463672882625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22164425263373139588707333 4155829736882463672882625)
              ·
                refine ⟨3116872302661847754661969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155829736882463672882625 3116872302661847754661969)
                ·
                  refine ⟨2337654226996385815996477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3116872302661847754661969 2337654226996385815996477)
                  ·
                    refine ⟨876620335123644680998679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337654226996385815996477 876620335123644680998679)
                    ·
                      rfl

theorem cell22_2560818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_2560818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560818 prefixEnd_2560818 := by exact prefixLift 2560818
  have htrace : WordTrace (prefixWord ++ tailWord_2560818) baseStart_2560818 baseEnd_2560818 := by
    simpa [prefixWord, tailWord_2560818, baseEnd_2560818] using wordTrace_append hprefix tailTrace_2560818
  have hstable : (prefixWord ++ tailWord_2560818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560818).length < 2 ^ (prefixWord ++ tailWord_2560818).sum := by decide
  have hdescent : baseEnd_2560818 < baseStart_2560818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560820 : List Nat := [2, 5, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2560820 : Nat := 118140960795 + 2560820 * 2 ^ 59
def prefixEnd_2560820 : Nat := 4983230072969 + 3 ^ 40 * 2560820 * 2
def baseEnd_2560820 : Nat := 292207006588172447482891

theorem tailTrace_2560820 : CollatzResearch.WordTrace tailWord_2560820 prefixEnd_2560820 292207006588172447482891 := by
  unfold tailWord_2560820
  simp only [CollatzResearch.WordTrace]
  refine ⟨46700389291296984040819957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62267185721729312054426609 46700389291296984040819957)
  ·
    refine ⟨4378161496059092253826871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46700389291296984040819957 4378161496059092253826871)
    ·
      refine ⟨6567242244088638380740307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4378161496059092253826871 6567242244088638380740307)
      ·
        refine ⟨9850863366132957571110461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567242244088638380740307 9850863366132957571110461)
        ·
          refine ⟨3694073762299859089166423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9850863366132957571110461 3694073762299859089166423)
          ·
            refine ⟨5541110643449788633749635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3694073762299859089166423 5541110643449788633749635)
            ·
              refine ⟨8311665965174682950624453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541110643449788633749635 8311665965174682950624453)
              ·
                refine ⟨1558437368470253053242085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8311665965174682950624453 1558437368470253053242085)
                ·
                  refine ⟨292207006588172447482891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1558437368470253053242085 292207006588172447482891)
                  ·
                    rfl

theorem cell22_2560820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2560820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560820 prefixEnd_2560820 := by exact prefixLift 2560820
  have htrace : WordTrace (prefixWord ++ tailWord_2560820) baseStart_2560820 baseEnd_2560820 := by
    simpa [prefixWord, tailWord_2560820, baseEnd_2560820] using wordTrace_append hprefix tailTrace_2560820
  have hstable : (prefixWord ++ tailWord_2560820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560820).length < 2 ^ (prefixWord ++ tailWord_2560820).sum := by decide
  have hdescent : baseEnd_2560820 < baseStart_2560820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560831 : List Nat := [1, 1, 2, 2, 5, 3, 1, 7]
def baseStart_2560831 : Nat := 118140960795 + 2560831 * 2 ^ 59
def prefixEnd_2560831 : Nat := 4983230072969 + 3 ^ 40 * 2560831 * 2
def baseEnd_2560831 : Nat := 97402753921035220047071

theorem tailTrace_2560831 : CollatzResearch.WordTrace tailWord_2560831 prefixEnd_2560831 97402753921035220047071 := by
  unfold tailWord_2560831
  simp only [CollatzResearch.WordTrace]
  refine ⟨93401179785554116960290347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62267453190369411306860231 93401179785554116960290347)
  ·
    refine ⟨140101769678331175440435521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93401179785554116960290347 140101769678331175440435521)
    ·
      refine ⟨105076327258748381580326641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140101769678331175440435521 105076327258748381580326641)
      ·
        refine ⟨78807245444061286185244981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105076327258748381580326641 78807245444061286185244981)
        ·
          refine ⟨7388179260380745579866717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78807245444061286185244981 7388179260380745579866717)
          ·
            refine ⟨2770567222642779592450019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7388179260380745579866717 2770567222642779592450019)
            ·
              refine ⟨4155850833964169388675029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770567222642779592450019 4155850833964169388675029)
              ·
                refine ⟨97402753921035220047071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4155850833964169388675029 97402753921035220047071)
                ·
                  rfl

theorem cell22_2560831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 7].length) (baseStart_2560831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560831 prefixEnd_2560831 := by exact prefixLift 2560831
  have htrace : WordTrace (prefixWord ++ tailWord_2560831) baseStart_2560831 baseEnd_2560831 := by
    simpa [prefixWord, tailWord_2560831, baseEnd_2560831] using wordTrace_append hprefix tailTrace_2560831
  have hstable : (prefixWord ++ tailWord_2560831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560831).length < 2 ^ (prefixWord ++ tailWord_2560831).sum := by decide
  have hdescent : baseEnd_2560831 < baseStart_2560831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560914 : List Nat := [3, 2, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2560914 : Nat := 118140960795 + 2560914 * 2 ^ 59
def prefixEnd_2560914 : Nat := 4983230072969 + 3 ^ 40 * 2560914 * 2
def baseEnd_2560914 : Nat := 876653197885532430598385

theorem tailTrace_2560914 : CollatzResearch.WordTrace tailWord_2560914 prefixEnd_2560914 876653197885532430598385 := by
  unfold tailWord_2560914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23351051761063355533890449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62269471362835614757041197 23351051761063355533890449)
  ·
    refine ⟨17513288820797516650417837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23351051761063355533890449 17513288820797516650417837)
    ·
      refine ⟨6567483307799068743906689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17513288820797516650417837 6567483307799068743906689)
      ·
        refine ⟨4925612480849301557930017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6567483307799068743906689 4925612480849301557930017)
        ·
          refine ⟨3694209360636976168447513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4925612480849301557930017 3694209360636976168447513)
          ·
            refine ⟨2770657020477732126335635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3694209360636976168447513 2770657020477732126335635)
            ·
              refine ⟨4155985530716598189503453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770657020477732126335635 4155985530716598189503453)
              ·
                refine ⟨1558494574018724321063795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4155985530716598189503453 1558494574018724321063795)
                ·
                  refine ⟨2337741861028086481595693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558494574018724321063795 2337741861028086481595693)
                  ·
                    refine ⟨876653197885532430598385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337741861028086481595693 876653197885532430598385)
                    ·
                      rfl

theorem cell22_2560914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2560914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560914 prefixEnd_2560914 := by exact prefixLift 2560914
  have htrace : WordTrace (prefixWord ++ tailWord_2560914) baseStart_2560914 baseEnd_2560914 := by
    simpa [prefixWord, tailWord_2560914, baseEnd_2560914] using wordTrace_append hprefix tailTrace_2560914
  have hstable : (prefixWord ++ tailWord_2560914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560914).length < 2 ^ (prefixWord ++ tailWord_2560914).sum := by decide
  have hdescent : baseEnd_2560914 < baseStart_2560914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560957 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_2560957 : Nat := 118140960795 + 2560957 * 2 ^ 59
def prefixEnd_2560957 : Nat := 4983230072969 + 3 ^ 40 * 2560957 * 2
def baseEnd_2560957 : Nat := 876667917664294651773253

theorem tailTrace_2560957 : CollatzResearch.WordTrace tailWord_2560957 prefixEnd_2560957 876667917664294651773253 := by
  unfold tailWord_2560957
  simp only [CollatzResearch.WordTrace]
  refine ⟨93405775383097640479377125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62270516922065093652918083 93405775383097640479377125)
  ·
    refine ⟨17513582884330807589883211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93405775383097640479377125 17513582884330807589883211)
    ·
      refine ⟨26270374326496211384824817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17513582884330807589883211 26270374326496211384824817)
      ·
        refine ⟨19702780744872158538618613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26270374326496211384824817 19702780744872158538618613)
        ·
          refine ⟨1847135694831764862995495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19702780744872158538618613 1847135694831764862995495)
          ·
            refine ⟨2770703542247647294493243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847135694831764862995495 2770703542247647294493243)
            ·
              refine ⟨4156055313371470941739865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770703542247647294493243 4156055313371470941739865)
              ·
                refine ⟨3117041485028603206304899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4156055313371470941739865 3117041485028603206304899)
                ·
                  refine ⟨4675562227542904809457349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117041485028603206304899 4675562227542904809457349)
                  ·
                    refine ⟨876667917664294651773253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4675562227542904809457349 876667917664294651773253)
                    ·
                      rfl

theorem cell22_2560957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_2560957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560957 prefixEnd_2560957 := by exact prefixLift 2560957
  have htrace : WordTrace (prefixWord ++ tailWord_2560957) baseStart_2560957 baseEnd_2560957 := by
    simpa [prefixWord, tailWord_2560957, baseEnd_2560957] using wordTrace_append hprefix tailTrace_2560957
  have hstable : (prefixWord ++ tailWord_2560957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560957).length < 2 ^ (prefixWord ++ tailWord_2560957).sum := by decide
  have hdescent : baseEnd_2560957 < baseStart_2560957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561032 : List Nat := [2, 1, 3, 2, 1, 4, 2, 3, 1, 3]
def baseStart_2561032 : Nat := 118140960795 + 2561032 * 2 ^ 59
def prefixEnd_2561032 : Nat := 4983230072969 + 3 ^ 40 * 2561032 * 2
def baseEnd_2561032 : Nat := 876693591697019456148023

theorem tailTrace_2561032 : CollatzResearch.WordTrace tailWord_2561032 prefixEnd_2561032 876693591697019456148023 := by
  unfold tailWord_2561032
  simp only [CollatzResearch.WordTrace]
  refine ⟨46704255428912964144178675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62272340571883952192238233 46704255428912964144178675)
  ·
    refine ⟨70056383143369446216268013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46704255428912964144178675 70056383143369446216268013)
    ·
      refine ⟨26271143678763542331100505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70056383143369446216268013 26271143678763542331100505)
      ·
        refine ⟨19703357759072656748325379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26271143678763542331100505 19703357759072656748325379)
        ·
          refine ⟨29555036638608985122488069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19703357759072656748325379 29555036638608985122488069)
          ·
            refine ⟨5541569369739184710466513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29555036638608985122488069 5541569369739184710466513)
            ·
              refine ⟨4156177027304388532849885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5541569369739184710466513 4156177027304388532849885)
              ·
                refine ⟨1558566385239145699818707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4156177027304388532849885 1558566385239145699818707)
                ·
                  refine ⟨2337849577858718549728061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558566385239145699818707 2337849577858718549728061)
                  ·
                    refine ⟨876693591697019456148023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337849577858718549728061 876693591697019456148023)
                    ·
                      rfl

theorem cell22_2561032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_2561032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561032 prefixEnd_2561032 := by exact prefixLift 2561032
  have htrace : WordTrace (prefixWord ++ tailWord_2561032) baseStart_2561032 baseEnd_2561032 := by
    simpa [prefixWord, tailWord_2561032, baseEnd_2561032] using wordTrace_append hprefix tailTrace_2561032
  have hstable : (prefixWord ++ tailWord_2561032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561032).length < 2 ^ (prefixWord ++ tailWord_2561032).sum := by decide
  have hdescent : baseEnd_2561032 < baseStart_2561032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561045 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 5]
def baseStart_2561045 : Nat := 118140960795 + 2561045 * 2 ^ 59
def prefixEnd_2561045 : Nat := 4983230072969 + 3 ^ 40 * 2561045 * 2
def baseEnd_2561045 : Nat := 292232680620897251857661

theorem tailTrace_2561045 : CollatzResearch.WordTrace tailWord_2561045 prefixEnd_2561045 292232680620897251857661 := by
  unfold tailWord_2561045
  simp only [CollatzResearch.WordTrace]
  refine ⟨93408985006778831508580589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62272656671185887672387059 93408985006778831508580589)
  ·
    refine ⟨35028369377542061815717721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93408985006778831508580589 35028369377542061815717721)
    ·
      refine ⟨26271277033156546361788291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35028369377542061815717721 26271277033156546361788291)
      ·
        refine ⟨39406915549734819542682437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26271277033156546361788291 39406915549734819542682437)
        ·
          refine ⟨7388796665575278664252957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39406915549734819542682437 7388796665575278664252957)
          ·
            refine ⟨2770798749590729499094859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7388796665575278664252957 2770798749590729499094859)
            ·
              refine ⟨4156198124386094248642289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770798749590729499094859 4156198124386094248642289)
              ·
                refine ⟨3117148593289570686481717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4156198124386094248642289 3117148593289570686481717)
                ·
                  refine ⟨292232680620897251857661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117148593289570686481717 292232680620897251857661)
                  ·
                    rfl

theorem cell22_2561045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_2561045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561045 prefixEnd_2561045 := by exact prefixLift 2561045
  have htrace : WordTrace (prefixWord ++ tailWord_2561045) baseStart_2561045 baseEnd_2561045 := by
    simpa [prefixWord, tailWord_2561045, baseEnd_2561045] using wordTrace_append hprefix tailTrace_2561045
  have hstable : (prefixWord ++ tailWord_2561045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561045).length < 2 ^ (prefixWord ++ tailWord_2561045).sum := by decide
  have hdescent : baseEnd_2561045 < baseStart_2561045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561088 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 6, 3]
def baseStart_2561088 : Nat := 118140960795 + 2561088 * 2 ^ 59
def prefixEnd_2561088 : Nat := 4983230072969 + 3 ^ 40 * 2561088 * 2
def baseEnd_2561088 : Nat := 876712761641453976747851

theorem tailTrace_2561088 : CollatzResearch.WordTrace tailWord_2561088 prefixEnd_2561088 876712761641453976747851 := by
  unfold tailWord_2561088
  simp only [CollatzResearch.WordTrace]
  refine ⟨46705276672811524926197959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62273702230415366568263945 46705276672811524926197959)
  ·
    refine ⟨70057915009217287389296939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46705276672811524926197959 70057915009217287389296939)
    ·
      refine ⟨105086872513825931083945409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70057915009217287389296939 105086872513825931083945409)
      ·
        refine ⟨78815154385369448312959057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105086872513825931083945409 78815154385369448312959057)
        ·
          refine ⟨59111365789027086234719293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78815154385369448312959057 59111365789027086234719293)
          ·
            refine ⟨22166762170885157338019735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59111365789027086234719293 22166762170885157338019735)
            ·
              refine ⟨33250143256327736007029603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22166762170885157338019735 33250143256327736007029603)
              ·
                refine ⟨49875214884491604010544405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33250143256327736007029603 49875214884491604010544405)
                ·
                  refine ⟨2337900697710543937994269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49875214884491604010544405 2337900697710543937994269)
                  ·
                    refine ⟨876712761641453976747851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337900697710543937994269 876712761641453976747851)
                    ·
                      rfl

theorem cell22_2561088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_2561088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561088 prefixEnd_2561088 := by exact prefixLift 2561088
  have htrace : WordTrace (prefixWord ++ tailWord_2561088) baseStart_2561088 baseEnd_2561088 := by
    simpa [prefixWord, tailWord_2561088, baseEnd_2561088] using wordTrace_append hprefix tailTrace_2561088
  have hstable : (prefixWord ++ tailWord_2561088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561088).length < 2 ^ (prefixWord ++ tailWord_2561088).sum := by decide
  have hdescent : baseEnd_2561088 < baseStart_2561088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561180 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 5]
def baseStart_2561180 : Nat := 118140960795 + 2561180 * 2 ^ 59
def prefixEnd_2561180 : Nat := 4983230072969 + 3 ^ 40 * 2561180 * 2
def baseEnd_2561180 : Nat := 292248085040532134482523

theorem tailTrace_2561180 : CollatzResearch.WordTrace tailWord_2561180 prefixEnd_2561180 292248085040532134482523 := by
  unfold tailWord_2561180
  simp only [CollatzResearch.WordTrace]
  refine ⟨46706954430644874782372497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62275939240859833043163329 46706954430644874782372497)
  ·
    refine ⟨35030215822983656086779373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46706954430644874782372497 35030215822983656086779373)
    ·
      refine ⟨13136330933618871032542265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35030215822983656086779373 13136330933618871032542265)
      ·
        refine ⟨9852248200214153274406699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13136330933618871032542265 9852248200214153274406699)
        ·
          refine ⟨14778372300321229911610049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9852248200214153274406699 14778372300321229911610049)
          ·
            refine ⟨11083779225240922433707537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14778372300321229911610049 11083779225240922433707537)
            ·
              refine ⟨8312834418930691825280653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11083779225240922433707537 8312834418930691825280653)
              ·
                refine ⟨3117312907099009434480245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8312834418930691825280653 3117312907099009434480245)
                ·
                  refine ⟨292248085040532134482523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117312907099009434480245 292248085040532134482523)
                  ·
                    rfl

theorem cell22_2561180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_2561180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561180 prefixEnd_2561180 := by exact prefixLift 2561180
  have htrace : WordTrace (prefixWord ++ tailWord_2561180) baseStart_2561180 baseEnd_2561180 := by
    simpa [prefixWord, tailWord_2561180, baseEnd_2561180] using wordTrace_append hprefix tailTrace_2561180
  have hstable : (prefixWord ++ tailWord_2561180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561180).length < 2 ^ (prefixWord ++ tailWord_2561180).sum := by decide
  have hdescent : baseEnd_2561180 < baseStart_2561180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561223 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2561223 : Nat := 118140960795 + 2561223 * 2 ^ 59
def prefixEnd_2561223 : Nat := 4983230072969 + 3 ^ 40 * 2561223 * 2
def baseEnd_2561223 : Nat := 876758974900358624622437

theorem tailTrace_2561223 : CollatzResearch.WordTrace tailWord_2561223 prefixEnd_2561223 876758974900358624622437 := by
  unfold tailWord_2561223
  simp only [CollatzResearch.WordTrace]
  refine ⟨93415477200133967908560323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62276984800089311939040215 93415477200133967908560323)
  ·
    refine ⟨140123215800200951862840485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93415477200133967908560323 140123215800200951862840485)
    ·
      refine ⟨26273102962537678474282591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140123215800200951862840485 26273102962537678474282591)
      ·
        refine ⟨39409654443806517711423887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26273102962537678474282591 39409654443806517711423887)
        ·
          refine ⟨59114481665709776567135831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39409654443806517711423887 59114481665709776567135831)
          ·
            refine ⟨88671722498564664850703747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59114481665709776567135831 88671722498564664850703747)
            ·
              refine ⟨133007583747846997276055621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88671722498564664850703747 133007583747846997276055621)
              ·
                refine ⟨24938921952721311989260429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133007583747846997276055621 24938921952721311989260429)
                ·
                  refine ⟨9352095732270491995972661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24938921952721311989260429 9352095732270491995972661)
                  ·
                    refine ⟨876758974900358624622437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9352095732270491995972661 876758974900358624622437)
                    ·
                      rfl

theorem cell22_2561223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2561223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561223 prefixEnd_2561223 := by exact prefixLift 2561223
  have htrace : WordTrace (prefixWord ++ tailWord_2561223) baseStart_2561223 baseEnd_2561223 := by
    simpa [prefixWord, tailWord_2561223, baseEnd_2561223] using wordTrace_append hprefix tailTrace_2561223
  have hstable : (prefixWord ++ tailWord_2561223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561223).length < 2 ^ (prefixWord ++ tailWord_2561223).sum := by decide
  have hdescent : baseEnd_2561223 < baseStart_2561223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561360 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 6]
def baseStart_2561360 : Nat := 118140960795 + 2561360 * 2 ^ 59
def prefixEnd_2561360 : Nat := 4983230072969 + 3 ^ 40 * 2561360 * 2
def baseEnd_2561360 : Nat := 292268624266711977982339

theorem tailTrace_2561360 : CollatzResearch.WordTrace tailWord_2561360 prefixEnd_2561360 292268624266711977982339 := by
  unfold tailWord_2561360
  simp only [CollatzResearch.WordTrace]
  refine ⟨46710237000318820153148767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62280316000425093537531689 46710237000318820153148767)
  ·
    refine ⟨70065355500478230229723151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46710237000318820153148767 70065355500478230229723151)
    ·
      refine ⟨105098033250717345344584727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70065355500478230229723151 105098033250717345344584727)
      ·
        refine ⟨157647049876076018016877091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105098033250717345344584727 157647049876076018016877091)
        ·
          refine ⟨236470574814114027025315637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157647049876076018016877091 236470574814114027025315637)
          ·
            refine ⟨22169116388823190033623341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236470574814114027025315637 22169116388823190033623341)
            ·
              refine ⟨8313418645808696262608753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22169116388823190033623341 8313418645808696262608753)
              ·
                refine ⟨6235063984356522196956565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8313418645808696262608753 6235063984356522196956565)
                ·
                  refine ⟨292268624266711977982339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6235063984356522196956565 292268624266711977982339)
                  ·
                    rfl

theorem cell22_2561360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_2561360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561360 prefixEnd_2561360 := by exact prefixLift 2561360
  have htrace : WordTrace (prefixWord ++ tailWord_2561360) baseStart_2561360 baseEnd_2561360 := by
    simpa [prefixWord, tailWord_2561360, baseEnd_2561360] using wordTrace_append hprefix tailTrace_2561360
  have hstable : (prefixWord ++ tailWord_2561360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561360).length < 2 ^ (prefixWord ++ tailWord_2561360).sum := by decide
  have hdescent : baseEnd_2561360 < baseStart_2561360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561362 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2561362 : Nat := 118140960795 + 2561362 * 2 ^ 59
def prefixEnd_2561362 : Nat := 4983230072969 + 3 ^ 40 * 2561362 * 2
def baseEnd_2561362 : Nat := 876806557441008595397011

theorem tailTrace_2561362 : CollatzResearch.WordTrace tailWord_2561362 prefixEnd_2561362 876806557441008595397011 := by
  unfold tailWord_2561362
  simp only [CollatzResearch.WordTrace]
  refine ⟨23355136736657598661967585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62280364631086929765246893 23355136736657598661967585)
  ·
    refine ⟨17516352552493198996475689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23355136736657598661967585 17516352552493198996475689)
    ·
      refine ⟨13137264414369899247356767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17516352552493198996475689 13137264414369899247356767)
      ·
        refine ⟨19705896621554848871035151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13137264414369899247356767 19705896621554848871035151)
        ·
          refine ⟨29558844932332273306552727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19705896621554848871035151 29558844932332273306552727)
          ·
            refine ⟨44338267398498409959829091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29558844932332273306552727 44338267398498409959829091)
            ·
              refine ⟨66507401097747614939743637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44338267398498409959829091 66507401097747614939743637)
              ·
                refine ⟨3117534426456919450300483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66507401097747614939743637 3117534426456919450300483)
                ·
                  refine ⟨4676301639685379175450725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117534426456919450300483 4676301639685379175450725)
                  ·
                    refine ⟨876806557441008595397011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4676301639685379175450725 876806557441008595397011)
                    ·
                      rfl

theorem cell22_2561362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2561362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561362 prefixEnd_2561362 := by exact prefixLift 2561362
  have htrace : WordTrace (prefixWord ++ tailWord_2561362) baseStart_2561362 baseEnd_2561362 := by
    simpa [prefixWord, tailWord_2561362, baseEnd_2561362] using wordTrace_append hprefix tailTrace_2561362
  have hstable : (prefixWord ++ tailWord_2561362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561362).length < 2 ^ (prefixWord ++ tailWord_2561362).sum := by decide
  have hdescent : baseEnd_2561362 < baseStart_2561362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561379 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 1, 4]
def baseStart_2561379 : Nat := 118140960795 + 2561379 * 2 ^ 59
def prefixEnd_2561379 : Nat := 4983230072969 + 3 ^ 40 * 2561379 * 2
def baseEnd_2561379 : Nat := 876812376888426217721959

theorem tailTrace_2561379 : CollatzResearch.WordTrace tailWord_2561379 prefixEnd_2561379 876812376888426217721959 := by
  unfold tailWord_2561379
  simp only [CollatzResearch.WordTrace]
  refine ⟨93421166987568806551239191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62280777991712537700826127 93421166987568806551239191)
  ·
    refine ⟨140131750481353209826858787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93421166987568806551239191 140131750481353209826858787)
    ·
      refine ⟨210197625722029814740288181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140131750481353209826858787 210197625722029814740288181)
      ·
        refine ⟨19706027411440295131902017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210197625722029814740288181 19706027411440295131902017)
        ·
          refine ⟨14779520558580221348926513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19706027411440295131902017 14779520558580221348926513)
          ·
            refine ⟨11084640418935166011694885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14779520558580221348926513 11084640418935166011694885)
            ·
              refine ⟨2078370078550343627192791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11084640418935166011694885 2078370078550343627192791)
              ·
                refine ⟨3117555117825515440789187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078370078550343627192791 3117555117825515440789187)
                ·
                  refine ⟨4676332676738273161183781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117555117825515440789187 4676332676738273161183781)
                  ·
                    refine ⟨876812376888426217721959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4676332676738273161183781 876812376888426217721959)
                    ·
                      rfl

theorem cell22_2561379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 4].length) (baseStart_2561379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561379 prefixEnd_2561379 := by exact prefixLift 2561379
  have htrace : WordTrace (prefixWord ++ tailWord_2561379) baseStart_2561379 baseEnd_2561379 := by
    simpa [prefixWord, tailWord_2561379, baseEnd_2561379] using wordTrace_append hprefix tailTrace_2561379
  have hstable : (prefixWord ++ tailWord_2561379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561379).length < 2 ^ (prefixWord ++ tailWord_2561379).sum := by decide
  have hdescent : baseEnd_2561379 < baseStart_2561379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561392 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 4, 3]
def baseStart_2561392 : Nat := 118140960795 + 2561392 * 2 ^ 59
def prefixEnd_2561392 : Nat := 4983230072969 + 3 ^ 40 * 2561392 * 2
def baseEnd_2561392 : Nat := 876816827054098517146919

theorem tailTrace_2561392 : CollatzResearch.WordTrace tailWord_2561392 prefixEnd_2561392 876816827054098517146919 := by
  unfold tailWord_2561392
  simp only [CollatzResearch.WordTrace]
  refine ⟨46710820568260854885731215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62281094091014473180974953 46710820568260854885731215)
  ·
    refine ⟨70066230852391282328596823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46710820568260854885731215 70066230852391282328596823)
    ·
      refine ⟨105099346278586923492895235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70066230852391282328596823 105099346278586923492895235)
      ·
        refine ⟨157649019417880385239342853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105099346278586923492895235 157649019417880385239342853)
        ·
          refine ⟨29559191140852572232376785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157649019417880385239342853 29559191140852572232376785)
          ·
            refine ⟨22169393355639429174282589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29559191140852572232376785 22169393355639429174282589)
            ·
              refine ⟨8313522508364785940355971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22169393355639429174282589 8313522508364785940355971)
              ·
                refine ⟨12470283762547178910533957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8313522508364785940355971 12470283762547178910533957)
                ·
                  refine ⟨2338178205477596045725117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12470283762547178910533957 2338178205477596045725117)
                  ·
                    refine ⟨876816827054098517146919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338178205477596045725117 876816827054098517146919)
                    ·
                      rfl

theorem cell22_2561392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_2561392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561392 prefixEnd_2561392 := by exact prefixLift 2561392
  have htrace : WordTrace (prefixWord ++ tailWord_2561392) baseStart_2561392 baseEnd_2561392 := by
    simpa [prefixWord, tailWord_2561392, baseEnd_2561392] using wordTrace_append hprefix tailTrace_2561392
  have hstable : (prefixWord ++ tailWord_2561392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561392).length < 2 ^ (prefixWord ++ tailWord_2561392).sum := by decide
  have hdescent : baseEnd_2561392 < baseStart_2561392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561405 : List Nat := [1, 4, 1, 1, 2, 2, 2, 9]
def baseStart_2561405 : Nat := 118140960795 + 2561405 * 2 ^ 59
def prefixEnd_2561405 : Nat := 4983230072969 + 3 ^ 40 * 2561405 * 2
def baseEnd_2561405 : Nat := 97424586357752312952431

theorem tailTrace_2561405 : CollatzResearch.WordTrace tailWord_2561405 prefixEnd_2561405 97424586357752312952431 := by
  unfold tailWord_2561405
  simp only [CollatzResearch.WordTrace]
  refine ⟨93422115285474612991685669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62281410190316408661123779 93422115285474612991685669)
  ·
    refine ⟨17516646616026489935941063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93422115285474612991685669 17516646616026489935941063)
    ·
      refine ⟨26274969924039734903911595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17516646616026489935941063 26274969924039734903911595)
      ·
        refine ⟨39412454886059602355867393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26274969924039734903911595 39412454886059602355867393)
        ·
          refine ⟨29559341164544701766900545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39412454886059602355867393 29559341164544701766900545)
          ·
            refine ⟨22169505873408526325175409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29559341164544701766900545 22169505873408526325175409)
            ·
              refine ⟨16627129405056394743881557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22169505873408526325175409 16627129405056394743881557)
              ·
                refine ⟨97424586357752312952431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16627129405056394743881557 97424586357752312952431)
                ·
                  rfl

theorem cell22_2561405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 9].length) (baseStart_2561405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561405 prefixEnd_2561405 := by exact prefixLift 2561405
  have htrace : WordTrace (prefixWord ++ tailWord_2561405) baseStart_2561405 baseEnd_2561405 := by
    simpa [prefixWord, tailWord_2561405, baseEnd_2561405] using wordTrace_append hprefix tailTrace_2561405
  have hstable : (prefixWord ++ tailWord_2561405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561405).length < 2 ^ (prefixWord ++ tailWord_2561405).sum := by decide
  have hdescent : baseEnd_2561405 < baseStart_2561405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561420 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_2561420 : Nat := 118140960795 + 2561420 * 2 ^ 59
def prefixEnd_2561420 : Nat := 4983230072969 + 3 ^ 40 * 2561420 * 2
def baseEnd_2561420 : Nat := 876826412026315777446833

theorem tailTrace_2561420 : CollatzResearch.WordTrace tailWord_2561420 prefixEnd_2561420 876826412026315777446833 := by
  unfold tailWord_2561420
  simp only [CollatzResearch.WordTrace]
  refine ⟨46711331190210135276740857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62281774920280180368987809 46711331190210135276740857)
  ·
    refine ⟨35033498392657601457555643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46711331190210135276740857 35033498392657601457555643)
    ·
      refine ⟨52550247588986402186333465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35033498392657601457555643 52550247588986402186333465)
      ·
        refine ⟨39412685691739801639750099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52550247588986402186333465 39412685691739801639750099)
        ·
          refine ⟨59119028537609702459625149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39412685691739801639750099 59119028537609702459625149)
          ·
            refine ⟨22169635701603638422359431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59119028537609702459625149 22169635701603638422359431)
            ·
              refine ⟨33254453552405457633539147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22169635701603638422359431 33254453552405457633539147)
              ·
                refine ⟨49881680328608186450308721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33254453552405457633539147 49881680328608186450308721)
                ·
                  refine ⟨37411260246456139837731541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49881680328608186450308721 37411260246456139837731541)
                  ·
                    refine ⟨876826412026315777446833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37411260246456139837731541 876826412026315777446833)
                    ·
                      rfl

theorem cell22_2561420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_2561420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561420 prefixEnd_2561420 := by exact prefixLift 2561420
  have htrace : WordTrace (prefixWord ++ tailWord_2561420) baseStart_2561420 baseEnd_2561420 := by
    simpa [prefixWord, tailWord_2561420, baseEnd_2561420] using wordTrace_append hprefix tailTrace_2561420
  have hstable : (prefixWord ++ tailWord_2561420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561420).length < 2 ^ (prefixWord ++ tailWord_2561420).sum := by decide
  have hdescent : baseEnd_2561420 < baseStart_2561420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561512 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 6]
def baseStart_2561512 : Nat := 118140960795 + 2561512 * 2 ^ 59
def prefixEnd_2561512 : Nat := 4983230072969 + 3 ^ 40 * 2561512 * 2
def baseEnd_2561512 : Nat := 292285968502152734715517

theorem tailTrace_2561512 : CollatzResearch.WordTrace tailWord_2561512 prefixEnd_2561512 292285968502152734715517 := by
  unfold tailWord_2561512
  simp only [CollatzResearch.WordTrace]
  refine ⟨46713008948043485132915395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62284011930724646843887193 46713008948043485132915395)
  ·
    refine ⟨70069513422065227699373093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46713008948043485132915395 70069513422065227699373093)
    ·
      refine ⟨13138033766637230193632455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70069513422065227699373093 13138033766637230193632455)
      ·
        refine ⟨19707050649955845290448683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13138033766637230193632455 19707050649955845290448683)
        ·
          refine ⟨29560575974933767935673025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19707050649955845290448683 29560575974933767935673025)
          ·
            refine ⟨22170431981200325951754769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29560575974933767935673025 22170431981200325951754769)
            ·
              refine ⟨16627823985900244463816077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22170431981200325951754769 16627823985900244463816077)
              ·
                refine ⟨6235433994712591673931029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16627823985900244463816077 6235433994712591673931029)
                ·
                  refine ⟨292285968502152734715517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6235433994712591673931029 292285968502152734715517)
                  ·
                    rfl

theorem cell22_2561512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_2561512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561512 prefixEnd_2561512 := by exact prefixLift 2561512
  have htrace : WordTrace (prefixWord ++ tailWord_2561512) baseStart_2561512 baseEnd_2561512 := by
    simpa [prefixWord, tailWord_2561512, baseEnd_2561512] using wordTrace_append hprefix tailTrace_2561512
  have hstable : (prefixWord ++ tailWord_2561512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561512).length < 2 ^ (prefixWord ++ tailWord_2561512).sum := by decide
  have hdescent : baseEnd_2561512 < baseStart_2561512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561546 : List Nat := [3, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_2561546 : Nat := 118140960795 + 2561546 * 2 ^ 59
def prefixEnd_2561546 : Nat := 4983230072969 + 3 ^ 40 * 2561546 * 2
def baseEnd_2561546 : Nat := 292289848133764482932149

theorem tailTrace_2561546 : CollatzResearch.WordTrace tailWord_2561546 prefixEnd_2561546 292289848133764482932149 := by
  unfold tailWord_2561546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23356814494490948518142123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62284838651975862715045661 23356814494490948518142123)
  ·
    refine ⟨35035221741736422777213185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23356814494490948518142123 35035221741736422777213185)
    ·
      refine ⟨26276416306302317082909889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35035221741736422777213185 26276416306302317082909889)
      ·
        refine ⟨19707312229726737812182417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26276416306302317082909889 19707312229726737812182417)
        ·
          refine ⟨14780484172295053359136813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19707312229726737812182417 14780484172295053359136813)
          ·
            refine ⟨5542681564610645009676305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14780484172295053359136813 5542681564610645009676305)
            ·
              refine ⟨4157011173457983757257229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5542681564610645009676305 4157011173457983757257229)
              ·
                refine ⟨1558879190046743908971461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4157011173457983757257229 1558879190046743908971461)
                ·
                  refine ⟨292289848133764482932149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1558879190046743908971461 292289848133764482932149)
                  ·
                    rfl

theorem cell22_2561546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_2561546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561546 prefixEnd_2561546 := by exact prefixLift 2561546
  have htrace : WordTrace (prefixWord ++ tailWord_2561546) baseStart_2561546 baseEnd_2561546 := by
    simpa [prefixWord, tailWord_2561546, baseEnd_2561546] using wordTrace_append hprefix tailTrace_2561546
  have hstable : (prefixWord ++ tailWord_2561546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561546).length < 2 ^ (prefixWord ++ tailWord_2561546).sum := by decide
  have hdescent : baseEnd_2561546 < baseStart_2561546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561548 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_2561548 : Nat := 118140960795 + 2561548 * 2 ^ 59
def prefixEnd_2561548 : Nat := 4983230072969 + 3 ^ 40 * 2561548 * 2
def baseEnd_2561548 : Nat := 876870229042166110246441

theorem tailTrace_2561548 : CollatzResearch.WordTrace tailWord_2561548 prefixEnd_2561548 876870229042166110246441 := by
  unfold tailWord_2561548
  simp only [CollatzResearch.WordTrace]
  refine ⟨46713665461978274207070649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62284887282637698942760865 46713665461978274207070649)
  ·
    refine ⟨35035249096483705655302987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46713665461978274207070649 35035249096483705655302987)
    ·
      refine ⟨52552873644725558482954481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35035249096483705655302987 52552873644725558482954481)
      ·
        refine ⟨39414655233544168862215861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52552873644725558482954481 39414655233544168862215861)
        ·
          refine ⟨3695123928144765830832737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39414655233544168862215861 3695123928144765830832737)
          ·
            refine ⟨2771342946108574373124553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3695123928144765830832737 2771342946108574373124553)
            ·
              refine ⟨2078507209581430779843415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771342946108574373124553 2078507209581430779843415)
              ·
                refine ⟨3117760814372146169765123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078507209581430779843415 3117760814372146169765123)
                ·
                  refine ⟨4676641221558219254647685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117760814372146169765123 4676641221558219254647685)
                  ·
                    refine ⟨876870229042166110246441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4676641221558219254647685 876870229042166110246441)
                    ·
                      rfl

theorem cell22_2561548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_2561548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561548 prefixEnd_2561548 := by exact prefixLift 2561548
  have htrace : WordTrace (prefixWord ++ tailWord_2561548) baseStart_2561548 baseEnd_2561548 := by
    simpa [prefixWord, tailWord_2561548, baseEnd_2561548] using wordTrace_append hprefix tailTrace_2561548
  have hstable : (prefixWord ++ tailWord_2561548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561548).length < 2 ^ (prefixWord ++ tailWord_2561548).sum := by decide
  have hdescent : baseEnd_2561548 < baseStart_2561548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561557 : List Nat := [1, 3, 2, 1, 3, 3, 9]
def baseStart_2561557 : Nat := 118140960795 + 2561557 * 2 ^ 59
def prefixEnd_2561557 : Nat := 4983230072969 + 3 ^ 40 * 2561557 * 2
def baseEnd_2561557 : Nat := 32476789256521966176719

theorem tailTrace_2561557 : CollatzResearch.WordTrace tailWord_2561557 prefixEnd_2561557 32476789256521966176719 := by
  unfold tailWord_2561557
  simp only [CollatzResearch.WordTrace]
  refine ⟨93427659180923942951218925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62285106120615961967479283 93427659180923942951218925)
  ·
    refine ⟨35035372192846478606707097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93427659180923942951218925 35035372192846478606707097)
    ·
      refine ⟨26276529144634858955030323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35035372192846478606707097 26276529144634858955030323)
      ·
        refine ⟨39414793716952288432545485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26276529144634858955030323 39414793716952288432545485)
        ·
          refine ⟨14780547643857108162204557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39414793716952288432545485 14780547643857108162204557)
          ·
            refine ⟨5542705366446415560826709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14780547643857108162204557 5542705366446415560826709)
            ·
              refine ⟨32476789256521966176719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5542705366446415560826709 32476789256521966176719)
              ·
                rfl

theorem cell22_2561557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 9].length) (baseStart_2561557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561557 prefixEnd_2561557 := by exact prefixLift 2561557
  have htrace : WordTrace (prefixWord ++ tailWord_2561557) baseStart_2561557 baseEnd_2561557 := by
    simpa [prefixWord, tailWord_2561557, baseEnd_2561557] using wordTrace_append hprefix tailTrace_2561557
  have hstable : (prefixWord ++ tailWord_2561557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561557).length < 2 ^ (prefixWord ++ tailWord_2561557).sum := by decide
  have hdescent : baseEnd_2561557 < baseStart_2561557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561578 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2561578 : Nat := 118140960795 + 2561578 * 2 ^ 59
def prefixEnd_2561578 : Nat := 4983230072969 + 3 ^ 40 * 2561578 * 2
def baseEnd_2561578 : Nat := 876880498655256031996349

theorem tailTrace_2561578 : CollatzResearch.WordTrace tailWord_2561578 prefixEnd_2561578 876880498655256031996349 := by
  unfold tailWord_2561578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23357106278461965884433347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62285616742565242358488925 23357106278461965884433347)
  ·
    refine ⟨35035659417692948826650021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23357106278461965884433347 35035659417692948826650021)
    ·
      refine ⟨6569186140817427904996879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35035659417692948826650021 6569186140817427904996879)
      ·
        refine ⟨9853779211226141857495319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569186140817427904996879 9853779211226141857495319)
        ·
          refine ⟨14780668816839212786242979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853779211226141857495319 14780668816839212786242979)
          ·
            refine ⟨22171003225258819179364469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14780668816839212786242979 22171003225258819179364469)
            ·
              refine ⟨2078531552368014298065419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22171003225258819179364469 2078531552368014298065419)
              ·
                refine ⟨3117797328552021447098129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078531552368014298065419 3117797328552021447098129)
                ·
                  refine ⟨2338347996414016085323597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3117797328552021447098129 2338347996414016085323597)
                  ·
                    refine ⟨876880498655256031996349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338347996414016085323597 876880498655256031996349)
                    ·
                      rfl

theorem cell22_2561578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2561578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561578 prefixEnd_2561578 := by exact prefixLift 2561578
  have htrace : WordTrace (prefixWord ++ tailWord_2561578) baseStart_2561578 baseEnd_2561578 := by
    simpa [prefixWord, tailWord_2561578, baseEnd_2561578] using wordTrace_append hprefix tailTrace_2561578
  have hstable : (prefixWord ++ tailWord_2561578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561578).length < 2 ^ (prefixWord ++ tailWord_2561578).sum := by decide
  have hdescent : baseEnd_2561578 < baseStart_2561578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561629 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2561629 : Nat := 118140960795 + 2561629 * 2 ^ 59
def prefixEnd_2561629 : Nat := 4983230072969 + 3 ^ 40 * 2561629 * 2
def baseEnd_2561629 : Nat := 876897956997508898971193

theorem tailTrace_2561629 : CollatzResearch.WordTrace tailWord_2561629 prefixEnd_2561629 876897956997508898971193 := by
  unfold tailWord_2561629
  simp only [CollatzResearch.WordTrace]
  refine ⟨93430285236663099247839941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62286856824442066165226627 93430285236663099247839941)
  ·
    refine ⟨17518178481874331108969989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93430285236663099247839941 17518178481874331108969989)
    ·
      refine ⟨3284658465351437082931873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17518178481874331108969989 3284658465351437082931873)
      ·
        refine ⟨2463493849013577812198905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3284658465351437082931873 2463493849013577812198905)
        ·
          refine ⟨1847620386760183359149179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463493849013577812198905 1847620386760183359149179)
          ·
            refine ⟨2771430580140275038723769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847620386760183359149179 2771430580140275038723769)
            ·
              refine ⟨2078572935105206279042827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771430580140275038723769 2078572935105206279042827)
              ·
                refine ⟨3117859402657809418564241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078572935105206279042827 3117859402657809418564241)
                ·
                  refine ⟨2338394551993357063923181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3117859402657809418564241 2338394551993357063923181)
                  ·
                    refine ⟨876897956997508898971193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338394551993357063923181 876897956997508898971193)
                    ·
                      rfl

theorem cell22_2561629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2561629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561629 prefixEnd_2561629 := by exact prefixLift 2561629
  have htrace : WordTrace (prefixWord ++ tailWord_2561629) baseStart_2561629 baseEnd_2561629 := by
    simpa [prefixWord, tailWord_2561629, baseEnd_2561629] using wordTrace_append hprefix tailTrace_2561629
  have hstable : (prefixWord ++ tailWord_2561629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561629).length < 2 ^ (prefixWord ++ tailWord_2561629).sum := by decide
  have hdescent : baseEnd_2561629 < baseStart_2561629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561632 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_2561632 : Nat := 118140960795 + 2561632 * 2 ^ 59
def prefixEnd_2561632 : Nat := 4983230072969 + 3 ^ 40 * 2561632 * 2
def baseEnd_2561632 : Nat := 876898983958817891146183

theorem tailTrace_2561632 : CollatzResearch.WordTrace tailWord_2561632 prefixEnd_2561632 876898983958817891146183 := by
  unfold tailWord_2561632
  simp only [CollatzResearch.WordTrace]
  refine ⟨46715197327826115380099575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62286929770434820506799433 46715197327826115380099575)
  ·
    refine ⟨70072795991739173070149363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46715197327826115380099575 70072795991739173070149363)
    ·
      refine ⟨105109193987608759605224045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70072795991739173070149363 105109193987608759605224045)
      ·
        refine ⟨39415947745353284851959017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105109193987608759605224045 39415947745353284851959017)
        ·
          refine ⟨29561960809014963638969263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39415947745353284851959017 29561960809014963638969263)
          ·
            refine ⟨44342941213522445458453895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29561960809014963638969263 44342941213522445458453895)
            ·
              refine ⟨66514411820283668187680843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44342941213522445458453895 66514411820283668187680843)
              ·
                refine ⟨99771617730425502281521265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66514411820283668187680843 99771617730425502281521265)
                ·
                  refine ⟨74828713297819126711140949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99771617730425502281521265 74828713297819126711140949)
                  ·
                    refine ⟨876898983958817891146183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74828713297819126711140949 876898983958817891146183)
                    ·
                      rfl

theorem cell22_2561632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_2561632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561632 prefixEnd_2561632 := by exact prefixLift 2561632
  have htrace : WordTrace (prefixWord ++ tailWord_2561632) baseStart_2561632 baseEnd_2561632 := by
    simpa [prefixWord, tailWord_2561632, baseEnd_2561632] using wordTrace_append hprefix tailTrace_2561632
  have hstable : (prefixWord ++ tailWord_2561632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561632).length < 2 ^ (prefixWord ++ tailWord_2561632).sum := by decide
  have hdescent : baseEnd_2561632 < baseStart_2561632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561636 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 5]
def baseStart_2561636 : Nat := 118140960795 + 2561636 * 2 ^ 59
def prefixEnd_2561636 : Nat := 4983230072969 + 3 ^ 40 * 2561636 * 2
def baseEnd_2561636 : Nat := 292300117746854404682057

theorem tailTrace_2561636 : CollatzResearch.WordTrace tailWord_2561636 prefixEnd_2561636 292300117746854404682057 := by
  unfold tailWord_2561636
  simp only [CollatzResearch.WordTrace]
  refine ⟨46715270273818869721672381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62287027031758492962229841 46715270273818869721672381)
  ·
    refine ⟨17518226352682076145627143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46715270273818869721672381 17518226352682076145627143)
    ·
      refine ⟨26277339529023114218440715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17518226352682076145627143 26277339529023114218440715)
      ·
        refine ⟨39416009293534671327661073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26277339529023114218440715 39416009293534671327661073)
        ·
          refine ⟨29562006970151003495745805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39416009293534671327661073 29562006970151003495745805)
          ·
            refine ⟨11085752613806626310904677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29562006970151003495745805 11085752613806626310904677)
            ·
              refine ⟨2078578615088742433294627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11085752613806626310904677 2078578615088742433294627)
              ·
                refine ⟨3117867922633113649941941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078578615088742433294627 3117867922633113649941941)
                ·
                  refine ⟨292300117746854404682057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117867922633113649941941 292300117746854404682057)
                  ·
                    rfl

theorem cell22_2561636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_2561636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561636 prefixEnd_2561636 := by exact prefixLift 2561636
  have htrace : WordTrace (prefixWord ++ tailWord_2561636) baseStart_2561636 baseEnd_2561636 := by
    simpa [prefixWord, tailWord_2561636, baseEnd_2561636] using wordTrace_append hprefix tailTrace_2561636
  have hstable : (prefixWord ++ tailWord_2561636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561636).length < 2 ^ (prefixWord ++ tailWord_2561636).sum := by decide
  have hdescent : baseEnd_2561636 < baseStart_2561636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561647 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 8]
def baseStart_2561647 : Nat := 118140960795 + 2561647 * 2 ^ 59
def prefixEnd_2561647 : Nat := 4983230072969 + 3 ^ 40 * 2561647 * 2
def baseEnd_2561647 : Nat := 292301372921787617340379

theorem tailTrace_2561647 : CollatzResearch.WordTrace tailWord_2561647 prefixEnd_2561647 292301372921787617340379 := by
  unfold tailWord_2561647
  simp only [CollatzResearch.WordTrace]
  refine ⟨93430941750597888321995195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62287294500398592214663463 93430941750597888321995195)
  ·
    refine ⟨140146412625896832482992793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93430941750597888321995195 140146412625896832482992793)
    ·
      refine ⟨105109809469422624362244595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140146412625896832482992793 105109809469422624362244595)
      ·
        refine ⟨157664714204133936543366893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105109809469422624362244595 157664714204133936543366893)
        ·
          refine ⟨59124267826550226203762585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157664714204133936543366893 59124267826550226203762585)
          ·
            refine ⟨44343200869912669652821939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59124267826550226203762585 44343200869912669652821939)
            ·
              refine ⟨66514801304869004479232909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44343200869912669652821939 66514801304869004479232909)
              ·
                refine ⟨24943050489325876679712341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66514801304869004479232909 24943050489325876679712341)
                ·
                  refine ⟨292301372921787617340379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24943050489325876679712341 292301372921787617340379)
                  ·
                    rfl

theorem cell22_2561647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 8].length) (baseStart_2561647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561647 prefixEnd_2561647 := by exact prefixLift 2561647
  have htrace : WordTrace (prefixWord ++ tailWord_2561647) baseStart_2561647 baseEnd_2561647 := by
    simpa [prefixWord, tailWord_2561647, baseEnd_2561647] using wordTrace_append hprefix tailTrace_2561647
  have hstable : (prefixWord ++ tailWord_2561647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561647).length < 2 ^ (prefixWord ++ tailWord_2561647).sum := by decide
  have hdescent : baseEnd_2561647 < baseStart_2561647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561696 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_2561696 : Nat := 118140960795 + 2561696 * 2 ^ 59
def prefixEnd_2561696 : Nat := 4983230072969 + 3 ^ 40 * 2561696 * 2
def baseEnd_2561696 : Nat := 876920892466743057545987

theorem tailTrace_2561696 : CollatzResearch.WordTrace tailWord_2561696 prefixEnd_2561696 876920892466743057545987 := by
  unfold tailWord_2561696
  simp only [CollatzResearch.WordTrace]
  refine ⟨46716364463710184845264471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62288485951613579793685961 46716364463710184845264471)
  ·
    refine ⟨70074546695565277267896707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46716364463710184845264471 70074546695565277267896707)
    ·
      refine ⟨105111820043347915901845061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70074546695565277267896707 105111820043347915901845061)
      ·
        refine ⟨19708466258127734231595949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105111820043347915901845061 19708466258127734231595949)
        ·
          refine ⟨7390674846797900336848481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19708466258127734231595949 7390674846797900336848481)
          ·
            refine ⟨5543006135098425252636361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7390674846797900336848481 5543006135098425252636361)
            ·
              refine ⟨4157254601323818939477271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543006135098425252636361 4157254601323818939477271)
              ·
                refine ⟨6235881901985728409215907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157254601323818939477271 6235881901985728409215907)
                ·
                  refine ⟨9353822852978592613823861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6235881901985728409215907 9353822852978592613823861)
                  ·
                    refine ⟨876920892466743057545987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9353822852978592613823861 876920892466743057545987)
                    ·
                      rfl

theorem cell22_2561696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_2561696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561696 prefixEnd_2561696 := by exact prefixLift 2561696
  have htrace : WordTrace (prefixWord ++ tailWord_2561696) baseStart_2561696 baseEnd_2561696 := by
    simpa [prefixWord, tailWord_2561696, baseEnd_2561696] using wordTrace_append hprefix tailTrace_2561696
  have hstable : (prefixWord ++ tailWord_2561696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561696).length < 2 ^ (prefixWord ++ tailWord_2561696).sum := by decide
  have hdescent : baseEnd_2561696 < baseStart_2561696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561698 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2561698 : Nat := 118140960795 + 2561698 * 2 ^ 59
def prefixEnd_2561698 : Nat := 4983230072969 + 3 ^ 40 * 2561698 * 2
def baseEnd_2561698 : Nat := 292307192369205239665327

theorem tailTrace_2561698 : CollatzResearch.WordTrace tailWord_2561698 prefixEnd_2561698 292307192369205239665327 := by
  unfold tailWord_2561698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23358200468353281008025437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62288534582275416021401165 23358200468353281008025437)
  ·
    refine ⟨8759325175632480378009539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23358200468353281008025437 8759325175632480378009539)
    ·
      refine ⟨13138987763448720567014309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8759325175632480378009539 13138987763448720567014309)
      ·
        refine ⟨2463560205646635106315183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13138987763448720567014309 2463560205646635106315183)
        ·
          refine ⟨3695340308469952659472775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463560205646635106315183 3695340308469952659472775)
          ·
            refine ⟨5543010462704928989209163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695340308469952659472775 5543010462704928989209163)
            ·
              refine ⟨8314515694057393483813745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543010462704928989209163 8314515694057393483813745)
              ·
                refine ⟨6235886770543045112860309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8314515694057393483813745 6235886770543045112860309)
                ·
                  refine ⟨292307192369205239665327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6235886770543045112860309 292307192369205239665327)
                  ·
                    rfl

theorem cell22_2561698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2561698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561698 prefixEnd_2561698 := by exact prefixLift 2561698
  have htrace : WordTrace (prefixWord ++ tailWord_2561698) baseStart_2561698 baseEnd_2561698 := by
    simpa [prefixWord, tailWord_2561698, baseEnd_2561698] using wordTrace_append hprefix tailTrace_2561698
  have hstable : (prefixWord ++ tailWord_2561698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561698).length < 2 ^ (prefixWord ++ tailWord_2561698).sum := by decide
  have hdescent : baseEnd_2561698 < baseStart_2561698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561717 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2561717 : Nat := 118140960795 + 2561717 * 2 ^ 59
def prefixEnd_2561717 : Nat := 4983230072969 + 3 ^ 40 * 2561717 * 2
def baseEnd_2561717 : Nat := 876928081195906002770923

theorem tailTrace_2561717 : CollatzResearch.WordTrace tailWord_2561717 prefixEnd_2561717 876928081195906002770923 := by
  unfold tailWord_2561717
  simp only [CollatzResearch.WordTrace]
  refine ⟨93433494860344290277043405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62288996573562860184695603 93433494860344290277043405)
  ·
    refine ⟨35037560572629108853891277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93433494860344290277043405 35037560572629108853891277)
    ·
      refine ⟨13139085214735915820209229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35037560572629108853891277 13139085214735915820209229)
      ·
        refine ⟨4927156955525968432578461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13139085214735915820209229 4927156955525968432578461)
        ·
          refine ⟨1847683858322238162216923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4927156955525968432578461 1847683858322238162216923)
          ·
            refine ⟨2771525787483357243325385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847683858322238162216923 2771525787483357243325385)
            ·
              refine ⟨2078644340612517932494039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771525787483357243325385 2078644340612517932494039)
              ·
                refine ⟨3117966510918776898741059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078644340612517932494039 3117966510918776898741059)
                ·
                  refine ⟨4676949766378165348111589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117966510918776898741059 4676949766378165348111589)
                  ·
                    refine ⟨876928081195906002770923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4676949766378165348111589 876928081195906002770923)
                    ·
                      rfl

theorem cell22_2561717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2561717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561717 prefixEnd_2561717 := by exact prefixLift 2561717
  have htrace : WordTrace (prefixWord ++ tailWord_2561717) baseStart_2561717 baseEnd_2561717 := by
    simpa [prefixWord, tailWord_2561717, baseEnd_2561717] using wordTrace_append hprefix tailTrace_2561717
  have hstable : (prefixWord ++ tailWord_2561717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561717).length < 2 ^ (prefixWord ++ tailWord_2561717).sum := by decide
  have hdescent : baseEnd_2561717 < baseStart_2561717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561818 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_2561818 : Nat := 118140960795 + 2561818 * 2 ^ 59
def prefixEnd_2561818 : Nat := 4983230072969 + 3 ^ 40 * 2561818 * 2
def baseEnd_2561818 : Nat := 876962655559975405995613

theorem tailTrace_2561818 : CollatzResearch.WordTrace tailWord_2561818 prefixEnd_2561818 876962655559975405995613 := by
  unfold tailWord_2561818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23359294658244596131617527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62291452421985589684313405 23359294658244596131617527)
  ·
    refine ⟨35038941987366894197426291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23359294658244596131617527 35038941987366894197426291)
    ·
      refine ⟨52558412981050341296139437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35038941987366894197426291 52558412981050341296139437)
      ·
        refine ⟨19709404867893877986052289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52558412981050341296139437 19709404867893877986052289)
        ·
          refine ⟨14782053650920408489539217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19709404867893877986052289 14782053650920408489539217)
          ·
            refine ⟨11086540238190306367154413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14782053650920408489539217 11086540238190306367154413)
            ·
              refine ⟨4157452589321364887682905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11086540238190306367154413 4157452589321364887682905)
              ·
                refine ⟨3118089441991023665762179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157452589321364887682905 3118089441991023665762179)
                ·
                  refine ⟨4677134162986535498643269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118089441991023665762179 4677134162986535498643269)
                  ·
                    refine ⟨876962655559975405995613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4677134162986535498643269 876962655559975405995613)
                    ·
                      rfl

theorem cell22_2561818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_2561818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561818 prefixEnd_2561818 := by exact prefixLift 2561818
  have htrace : WordTrace (prefixWord ++ tailWord_2561818) baseStart_2561818 baseEnd_2561818 := by
    simpa [prefixWord, tailWord_2561818, baseEnd_2561818] using wordTrace_append hprefix tailTrace_2561818
  have hstable : (prefixWord ++ tailWord_2561818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561818).length < 2 ^ (prefixWord ++ tailWord_2561818).sum := by decide
  have hdescent : baseEnd_2561818 < baseStart_2561818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561848 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 2, 3]
def baseStart_2561848 : Nat := 118140960795 + 2561848 * 2 ^ 59
def prefixEnd_2561848 : Nat := 4983230072969 + 3 ^ 40 * 2561848 * 2
def baseEnd_2561848 : Nat := 876972925173065327745521

theorem tailTrace_2561848 : CollatzResearch.WordTrace tailWord_2561848 prefixEnd_2561848 876972925173065327745521 := by
  unfold tailWord_2561848
  simp only [CollatzResearch.WordTrace]
  refine ⟨46719136411434849825031099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62292181881913133100041465 46719136411434849825031099)
  ·
    refine ⟨70078704617152274737546649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46719136411434849825031099 70078704617152274737546649)
    ·
      refine ⟨52559028462864206053159987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70078704617152274737546649 52559028462864206053159987)
      ·
        refine ⟨78838542694296309079739981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52559028462864206053159987 78838542694296309079739981)
        ·
          refine ⟨29564453510361115904902493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78838542694296309079739981 29564453510361115904902493)
          ·
            refine ⟨11086670066385418464338435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29564453510361115904902493 11086670066385418464338435)
            ·
              refine ⟨16630005099578127696507653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11086670066385418464338435 16630005099578127696507653)
              ·
                refine ⟨3118125956170898943095185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16630005099578127696507653 3118125956170898943095185)
                ·
                  refine ⟨2338594467128174207321389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3118125956170898943095185 2338594467128174207321389)
                  ·
                    refine ⟨876972925173065327745521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338594467128174207321389 876972925173065327745521)
                    ·
                      rfl

theorem cell22_2561848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_2561848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561848 prefixEnd_2561848 := by exact prefixLift 2561848
  have htrace : WordTrace (prefixWord ++ tailWord_2561848) baseStart_2561848 baseEnd_2561848 := by
    simpa [prefixWord, tailWord_2561848, baseEnd_2561848] using wordTrace_append hprefix tailTrace_2561848
  have hstable : (prefixWord ++ tailWord_2561848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561848).length < 2 ^ (prefixWord ++ tailWord_2561848).sum := by decide
  have hdescent : baseEnd_2561848 < baseStart_2561848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2561850 : List Nat := [3, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_2561850 : Nat := 118140960795 + 2561850 * 2 ^ 59
def prefixEnd_2561850 : Nat := 4983230072969 + 3 ^ 40 * 2561850 * 2
def baseEnd_2561850 : Nat := 292324536604645996398505

theorem tailTrace_2561850 : CollatzResearch.WordTrace tailWord_2561850 prefixEnd_2561850 292324536604645996398505 := by
  unfold tailWord_2561850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23359586442215613497908751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62292230512574969327756669 23359586442215613497908751)
  ·
    refine ⟨35039379663323420246863127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23359586442215613497908751 35039379663323420246863127)
    ·
      refine ⟨52559069494985130370294691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35039379663323420246863127 52559069494985130370294691)
      ·
        refine ⟨78838604242477695555442037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52559069494985130370294691 78838604242477695555442037)
        ·
          refine ⟨7391119147732283958322691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78838604242477695555442037 7391119147732283958322691)
          ·
            refine ⟨11086678721598425937484037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391119147732283958322691 11086678721598425937484037)
            ·
              refine ⟨2078752260299704863278257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11086678721598425937484037 2078752260299704863278257)
              ·
                refine ⟨1559064195224778647458693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078752260299704863278257 1559064195224778647458693)
                ·
                  refine ⟨292324536604645996398505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1559064195224778647458693 292324536604645996398505)
                  ·
                    rfl

theorem cell22_2561850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_2561850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2561850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2561850 prefixEnd_2561850 := by exact prefixLift 2561850
  have htrace : WordTrace (prefixWord ++ tailWord_2561850) baseStart_2561850 baseEnd_2561850 := by
    simpa [prefixWord, tailWord_2561850, baseEnd_2561850] using wordTrace_append hprefix tailTrace_2561850
  have hstable : (prefixWord ++ tailWord_2561850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2561850).length < 2 ^ (prefixWord ++ tailWord_2561850).sum := by decide
  have hdescent : baseEnd_2561850 < baseStart_2561850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2561850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562013 : List Nat := [1, 4, 3, 1, 3, 10]
def baseStart_2562013 : Nat := 118140960795 + 2562013 * 2 ^ 59
def prefixEnd_2562013 : Nat := 4983230072969 + 3 ^ 40 * 2562013 * 2
def baseEnd_2562013 : Nat := 10827523556111850584815

theorem tailTrace_2562013 : CollatzResearch.WordTrace tailWord_2562013 prefixEnd_2562013 10827523556111850584815 := by
  unfold tailWord_2562013
  simp only [CollatzResearch.WordTrace]
  refine ⟨93444290867271932829818693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62296193911514621886545795 93444290867271932829818693)
  ·
    refine ⟨17520804537613487405591005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93444290867271932829818693 17520804537613487405591005)
    ·
      refine ⟨6570301701605057777096627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17520804537613487405591005 6570301701605057777096627)
      ·
        refine ⟨9855452552407586665644941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6570301701605057777096627 9855452552407586665644941)
        ·
          refine ⟨3695794707152844999616853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9855452552407586665644941 3695794707152844999616853)
          ·
            refine ⟨10827523556111850584815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3695794707152844999616853 10827523556111850584815)
            ·
              rfl

theorem cell22_2562013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 10].length) (baseStart_2562013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562013 prefixEnd_2562013 := by exact prefixLift 2562013
  have htrace : WordTrace (prefixWord ++ tailWord_2562013) baseStart_2562013 baseEnd_2562013 := by
    simpa [prefixWord, tailWord_2562013, baseEnd_2562013] using wordTrace_append hprefix tailTrace_2562013
  have hstable : (prefixWord ++ tailWord_2562013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562013).length < 2 ^ (prefixWord ++ tailWord_2562013).sum := by decide
  have hdescent : baseEnd_2562013 < baseStart_2562013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562028 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_2562028 : Nat := 118140960795 + 2562028 * 2 ^ 59
def prefixEnd_2562028 : Nat := 4983230072969 + 3 ^ 40 * 2562028 * 2
def baseEnd_2562028 : Nat := 877034542851604858244969

theorem tailTrace_2562028 : CollatzResearch.WordTrace tailWord_2562028 prefixEnd_2562028 877034542851604858244969 := by
  unfold tailWord_2562028
  simp only [CollatzResearch.WordTrace]
  refine ⟨46722418981108795195807369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62296558641478393594409825 46722418981108795195807369)
  ·
    refine ⟨35041814235831596396855527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46722418981108795195807369 35041814235831596396855527)
    ·
      refine ⟨52562721353747394595283291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35041814235831596396855527 52562721353747394595283291)
      ·
        refine ⟨78844082030621091892924937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52562721353747394595283291 78844082030621091892924937)
        ·
          refine ⟨59133061522965818919693703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78844082030621091892924937 59133061522965818919693703)
          ·
            refine ⟨88699592284448728379540555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59133061522965818919693703 88699592284448728379540555)
            ·
              refine ⟨133049388426673092569310833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88699592284448728379540555 133049388426673092569310833)
              ·
                refine ⟨99787041320004819426983125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133049388426673092569310833 99787041320004819426983125)
                ·
                  refine ⟨2338758780937612955319917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 99787041320004819426983125 2338758780937612955319917)
                  ·
                    refine ⟨877034542851604858244969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338758780937612955319917 877034542851604858244969)
                    ·
                      rfl

theorem cell22_2562028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_2562028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562028 prefixEnd_2562028 := by exact prefixLift 2562028
  have htrace : WordTrace (prefixWord ++ tailWord_2562028) baseStart_2562028 baseEnd_2562028 := by
    simpa [prefixWord, tailWord_2562028, baseEnd_2562028] using wordTrace_append hprefix tailTrace_2562028
  have hstable : (prefixWord ++ tailWord_2562028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562028).length < 2 ^ (prefixWord ++ tailWord_2562028).sum := by decide
  have hdescent : baseEnd_2562028 < baseStart_2562028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562030 : List Nat := [4, 1, 2, 1, 3, 3, 1, 7]
def baseStart_2562030 : Nat := 118140960795 + 2562030 * 2 ^ 59
def prefixEnd_2562030 : Nat := 4983230072969 + 3 ^ 40 * 2562030 * 2
def baseEnd_2562030 : Nat := 97448358610275279966107

theorem tailTrace_2562030 : CollatzResearch.WordTrace tailWord_2562030 prefixEnd_2562030 97448358610275279966107 := by
  unfold tailWord_2562030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11680613863526293091648443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62296607272140229822125029 11680613863526293091648443)
  ·
    refine ⟨17520920795289439637472665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11680613863526293091648443 17520920795289439637472665)
    ·
      refine ⟨13140690596467079728104499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17520920795289439637472665 13140690596467079728104499)
      ·
        refine ⟨19711035894700619592156749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13140690596467079728104499 19711035894700619592156749)
        ·
          refine ⟨7391638460512732347058781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19711035894700619592156749 7391638460512732347058781)
          ·
            refine ⟨2771864422692274630147043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7391638460512732347058781 2771864422692274630147043)
            ·
              refine ⟨4157796634038411945220565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771864422692274630147043 4157796634038411945220565)
              ·
                refine ⟨97448358610275279966107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4157796634038411945220565 97448358610275279966107)
                ·
                  rfl

theorem cell22_2562030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_2562030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562030 prefixEnd_2562030 := by exact prefixLift 2562030
  have htrace : WordTrace (prefixWord ++ tailWord_2562030) baseStart_2562030 baseEnd_2562030 := by
    simpa [prefixWord, tailWord_2562030, baseEnd_2562030] using wordTrace_append hprefix tailTrace_2562030
  have hstable : (prefixWord ++ tailWord_2562030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562030).length < 2 ^ (prefixWord ++ tailWord_2562030).sum := by decide
  have hdescent : baseEnd_2562030 < baseStart_2562030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562068 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2562068 : Nat := 118140960795 + 2562068 * 2 ^ 59
def prefixEnd_2562068 : Nat := 4983230072969 + 3 ^ 40 * 2562068 * 2
def baseEnd_2562068 : Nat := 877048235669058087244847

theorem tailTrace_2562068 : CollatzResearch.WordTrace tailWord_2562068 prefixEnd_2562068 877048235669058087244847 := by
  unfold tailWord_2562068
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723148441036338611535429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62297531254715118148713905 46723148441036338611535429)
  ·
    refine ⟨8760590332694313489662893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46723148441036338611535429 8760590332694313489662893)
    ·
      refine ⟨3285221374760367558623585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8760590332694313489662893 3285221374760367558623585)
      ·
        refine ⟨2463916031070275668967689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3285221374760367558623585 2463916031070275668967689)
        ·
          refine ⟨1847937023302706751725767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463916031070275668967689 1847937023302706751725767)
          ·
            refine ⟨2771905534954060127588651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847937023302706751725767 2771905534954060127588651)
            ·
              refine ⟨4157858302431090191382977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771905534954060127588651 4157858302431090191382977)
              ·
                refine ⟨3118393726823317643537233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157858302431090191382977 3118393726823317643537233)
                ·
                  refine ⟨2338795295117488232652925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3118393726823317643537233 2338795295117488232652925)
                  ·
                    refine ⟨877048235669058087244847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338795295117488232652925 877048235669058087244847)
                    ·
                      rfl

theorem cell22_2562068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2562068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562068 prefixEnd_2562068 := by exact prefixLift 2562068
  have htrace : WordTrace (prefixWord ++ tailWord_2562068) baseStart_2562068 baseEnd_2562068 := by
    simpa [prefixWord, tailWord_2562068, baseEnd_2562068] using wordTrace_append hprefix tailTrace_2562068
  have hstable : (prefixWord ++ tailWord_2562068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562068).length < 2 ^ (prefixWord ++ tailWord_2562068).sum := by decide
  have hdescent : baseEnd_2562068 < baseStart_2562068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562090 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2562090 : Nat := 118140960795 + 2562090 * 2 ^ 59
def prefixEnd_2562090 : Nat := 4983230072969 + 3 ^ 40 * 2562090 * 2
def baseEnd_2562090 : Nat := 877055766718657363194779

theorem tailTrace_2562090 : CollatzResearch.WordTrace tailWord_2562090 prefixEnd_2562090 877055766718657363194779 := by
  unfold tailWord_2562090
  simp only [CollatzResearch.WordTrace]
  refine ⟨23361774821998243745092931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62298066191995316653581149 23361774821998243745092931)
  ·
    refine ⟨35042662232997365617639397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23361774821998243745092931 35042662232997365617639397)
    ·
      refine ⟨6570499168687006053307387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35042662232997365617639397 6570499168687006053307387)
      ·
        refine ⟨9855748753030509079961081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6570499168687006053307387 9855748753030509079961081)
        ·
          refine ⟨7391811564772881809970811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9855748753030509079961081 7391811564772881809970811)
          ·
            refine ⟨11087717347159322714956217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391811564772881809970811 11087717347159322714956217)
            ·
              refine ⟨8315788010369492036217163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11087717347159322714956217 8315788010369492036217163)
              ·
                refine ⟨12473682015554238054325745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8315788010369492036217163 12473682015554238054325745)
                ·
                  refine ⟨9355261511665678540744309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12473682015554238054325745 9355261511665678540744309)
                  ·
                    refine ⟨877055766718657363194779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9355261511665678540744309 877055766718657363194779)
                    ·
                      rfl

theorem cell22_2562090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2562090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562090 prefixEnd_2562090 := by exact prefixLift 2562090
  have htrace : WordTrace (prefixWord ++ tailWord_2562090) baseStart_2562090 baseEnd_2562090 := by
    simpa [prefixWord, tailWord_2562090, baseEnd_2562090] using wordTrace_append hprefix tailTrace_2562090
  have hstable : (prefixWord ++ tailWord_2562090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562090).length < 2 ^ (prefixWord ++ tailWord_2562090).sum := by decide
  have hdescent : baseEnd_2562090 < baseStart_2562090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562103 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 6]
def baseStart_2562103 : Nat := 118140960795 + 2562103 * 2 ^ 59
def prefixEnd_2562103 : Nat := 4983230072969 + 3 ^ 40 * 2562103 * 2
def baseEnd_2562103 : Nat := 292353405628109887539913

theorem tailTrace_2562103 : CollatzResearch.WordTrace tailWord_2562103 prefixEnd_2562103 292353405628109887539913 := by
  unfold tailWord_2562103
  simp only [CollatzResearch.WordTrace]
  refine ⟨93447573436945878200594963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62298382291297252133729975 93447573436945878200594963)
  ·
    refine ⟨140171360155418817300892445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93447573436945878200594963 140171360155418817300892445)
    ·
      refine ⟨52564260058282056487834667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140171360155418817300892445 52564260058282056487834667)
      ·
        refine ⟨78846390087423084731752001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52564260058282056487834667 78846390087423084731752001)
        ·
          refine ⟨59134792565567313548814001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78846390087423084731752001 59134792565567313548814001)
          ·
            refine ⟨44351094424175485161610501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59134792565567313548814001 44351094424175485161610501)
            ·
              refine ⟨8315830204532903467801969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44351094424175485161610501 8315830204532903467801969)
              ·
                refine ⟨6236872653399677600851477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8315830204532903467801969 6236872653399677600851477)
                ·
                  refine ⟨292353405628109887539913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6236872653399677600851477 292353405628109887539913)
                  ·
                    rfl

theorem cell22_2562103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 6].length) (baseStart_2562103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562103 prefixEnd_2562103 := by exact prefixLift 2562103
  have htrace : WordTrace (prefixWord ++ tailWord_2562103) baseStart_2562103 baseEnd_2562103 := by
    simpa [prefixWord, tailWord_2562103, baseEnd_2562103] using wordTrace_append hprefix tailTrace_2562103
  have hstable : (prefixWord ++ tailWord_2562103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562103).length < 2 ^ (prefixWord ++ tailWord_2562103).sum := by decide
  have hdescent : baseEnd_2562103 < baseStart_2562103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562120 : List Nat := [2, 1, 3, 1, 1, 1, 2, 7, 4]
def baseStart_2562120 : Nat := 118140960795 + 2562120 * 2 ^ 59
def prefixEnd_2562120 : Nat := 4983230072969 + 3 ^ 40 * 2562120 * 2
def baseEnd_2562120 : Nat := 292355345443915761648229

theorem tailTrace_2562120 : CollatzResearch.WordTrace tailWord_2562120 prefixEnd_2562120 292355345443915761648229 := by
  unfold tailWord_2562120
  simp only [CollatzResearch.WordTrace]
  refine ⟨46724096738942145051981907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62298795651922860069309209 46724096738942145051981907)
  ·
    refine ⟨70086145108413217577972861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46724096738942145051981907 70086145108413217577972861)
    ·
      refine ⟨26282304415654956591739823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70086145108413217577972861 26282304415654956591739823)
      ·
        refine ⟨39423456623482434887609735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26282304415654956591739823 39423456623482434887609735)
        ·
          refine ⟨59135184935223652331414603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39423456623482434887609735 59135184935223652331414603)
          ·
            refine ⟨88702777402835478497121905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59135184935223652331414603 88702777402835478497121905)
            ·
              refine ⟨66527083052126608872841429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88702777402835478497121905 66527083052126608872841429)
              ·
                refine ⟨1559228509034217395457221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66527083052126608872841429 1559228509034217395457221)
                ·
                  refine ⟨292355345443915761648229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1559228509034217395457221 292355345443915761648229)
                  ·
                    rfl

theorem cell22_2562120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_2562120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562120 prefixEnd_2562120 := by exact prefixLift 2562120
  have htrace : WordTrace (prefixWord ++ tailWord_2562120) baseStart_2562120 baseEnd_2562120 := by
    simpa [prefixWord, tailWord_2562120, baseEnd_2562120] using wordTrace_append hprefix tailTrace_2562120
  have hstable : (prefixWord ++ tailWord_2562120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562120).length < 2 ^ (prefixWord ++ tailWord_2562120).sum := by decide
  have hdescent : baseEnd_2562120 < baseStart_2562120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562135 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 4, 3]
def baseStart_2562135 : Nat := 118140960795 + 2562135 * 2 ^ 59
def prefixEnd_2562135 : Nat := 4983230072969 + 3 ^ 40 * 2562135 * 2
def baseEnd_2562135 : Nat := 877071171138292245819641

theorem tailTrace_2562135 : CollatzResearch.WordTrace tailWord_2562135 prefixEnd_2562135 877071171138292245819641 := by
  unfold tailWord_2562135
  simp only [CollatzResearch.WordTrace]
  refine ⟨93448740572829947665759859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62299160381886631777173239 93448740572829947665759859)
  ·
    refine ⟨140173110859244921498639789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93448740572829947665759859 140173110859244921498639789)
    ·
      refine ⟨52564916572216845561989921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140173110859244921498639789 52564916572216845561989921)
      ·
        refine ⟨39423687429162634171492441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52564916572216845561989921 39423687429162634171492441)
        ·
          refine ⟨29567765571871975628619331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39423687429162634171492441 29567765571871975628619331)
          ·
            refine ⟨44351648357807963442928997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29567765571871975628619331 44351648357807963442928997)
            ·
              refine ⟨8315934067088993145549187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44351648357807963442928997 8315934067088993145549187)
              ·
                refine ⟨12473901100633489718323781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8315934067088993145549187 12473901100633489718323781)
                ·
                  refine ⟨2338856456368779322185709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12473901100633489718323781 2338856456368779322185709)
                  ·
                    refine ⟨877071171138292245819641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338856456368779322185709 877071171138292245819641)
                    ·
                      rfl

theorem cell22_2562135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_2562135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562135 prefixEnd_2562135 := by exact prefixLift 2562135
  have htrace : WordTrace (prefixWord ++ tailWord_2562135) baseStart_2562135 baseEnd_2562135 := by
    simpa [prefixWord, tailWord_2562135, baseEnd_2562135] using wordTrace_append hprefix tailTrace_2562135
  have hstable : (prefixWord ++ tailWord_2562135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562135).length < 2 ^ (prefixWord ++ tailWord_2562135).sum := by decide
  have hdescent : baseEnd_2562135 < baseStart_2562135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562137 : List Nat := [1, 2, 1, 2, 2, 1, 7, 2, 4]
def baseStart_2562137 : Nat := 118140960795 + 2562137 * 2 ^ 59
def prefixEnd_2562137 : Nat := 4983230072969 + 3 ^ 40 * 2562137 * 2
def baseEnd_2562137 : Nat := 292357285259721635756545

theorem tailTrace_2562137 : CollatzResearch.WordTrace tailWord_2562137 prefixEnd_2562137 292357285259721635756545 := by
  unfold tailWord_2562137
  simp only [CollatzResearch.WordTrace]
  refine ⟨93448813518822702007332665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62299209012548468004888443 93448813518822702007332665)
  ·
    refine ⟨70086610139117026505499499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93448813518822702007332665 70086610139117026505499499)
    ·
      refine ⟨105129915208675539758249249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70086610139117026505499499 105129915208675539758249249)
      ·
        refine ⟨78847436406506654818686937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105129915208675539758249249 78847436406506654818686937)
        ·
          refine ⟨59135577304879991114015203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78847436406506654818686937 59135577304879991114015203)
          ·
            refine ⟨88703365957319986671022805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59135577304879991114015203 88703365957319986671022805)
            ·
              refine ⟨2078985139624687187602097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 88703365957319986671022805 2078985139624687187602097)
              ·
                refine ⟨1559238854718515390701573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078985139624687187602097 1559238854718515390701573)
                ·
                  refine ⟨292357285259721635756545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1559238854718515390701573 292357285259721635756545)
                  ·
                    rfl

theorem cell22_2562137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_2562137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562137 prefixEnd_2562137 := by exact prefixLift 2562137
  have htrace : WordTrace (prefixWord ++ tailWord_2562137) baseStart_2562137 baseEnd_2562137 := by
    simpa [prefixWord, tailWord_2562137, baseEnd_2562137] using wordTrace_append hprefix tailTrace_2562137
  have hstable : (prefixWord ++ tailWord_2562137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562137).length < 2 ^ (prefixWord ++ tailWord_2562137).sum := by decide
  have hdescent : baseEnd_2562137 < baseStart_2562137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562148 : List Nat := [2, 3, 1, 1, 2, 1, 3, 9]
def baseStart_2562148 : Nat := 118140960795 + 2562148 * 2 ^ 59
def prefixEnd_2562148 : Nat := 4983230072969 + 3 ^ 40 * 2562148 * 2
def baseEnd_2562148 : Nat := 97452846811551616138289

theorem tailTrace_2562148 : CollatzResearch.WordTrace tailWord_2562148 prefixEnd_2562148 97452846811551616138289 := by
  unfold tailWord_2562148
  simp only [CollatzResearch.WordTrace]
  refine ⟨46724607360891425442991549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62299476481188567257322065 46724607360891425442991549)
  ·
    refine ⟨17521727760334284541121831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46724607360891425442991549 17521727760334284541121831)
    ·
      refine ⟨26282591640501426811682747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17521727760334284541121831 26282591640501426811682747)
      ·
        refine ⟨39423887460752140217524121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26282591640501426811682747 39423887460752140217524121)
        ·
          refine ⟨29567915595564105163143091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39423887460752140217524121 29567915595564105163143091)
          ·
            refine ⟨44351873393346157744714637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29567915595564105163143091 44351873393346157744714637)
            ·
              refine ⟨16631952522504809154267989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44351873393346157744714637 16631952522504809154267989)
              ·
                refine ⟨97452846811551616138289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16631952522504809154267989 97452846811551616138289)
                ·
                  rfl

theorem cell22_2562148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 9].length) (baseStart_2562148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562148 prefixEnd_2562148 := by exact prefixLift 2562148
  have htrace : WordTrace (prefixWord ++ tailWord_2562148) baseStart_2562148 baseEnd_2562148 := by
    simpa [prefixWord, tailWord_2562148, baseEnd_2562148] using wordTrace_append hprefix tailTrace_2562148
  have hstable : (prefixWord ++ tailWord_2562148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562148).length < 2 ^ (prefixWord ++ tailWord_2562148).sum := by decide
  have hdescent : baseEnd_2562148 < baseStart_2562148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562244 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 5]
def baseStart_2562244 : Nat := 118140960795 + 2562244 * 2 ^ 59
def prefixEnd_2562244 : Nat := 4983230072969 + 3 ^ 40 * 2562244 * 2
def baseEnd_2562244 : Nat := 292369494688617431614769

theorem tailTrace_2562244 : CollatzResearch.WordTrace tailWord_2562244 prefixEnd_2562244 292369494688617431614769 := by
  unfold tailWord_2562244
  simp only [CollatzResearch.WordTrace]
  refine ⟨46726358064717529640738893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62301810752956706187651857 46726358064717529640738893)
  ·
    refine ⟨17522384274269073615277085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46726358064717529640738893 17522384274269073615277085)
    ·
      refine ⟨6570894102850902605728907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17522384274269073615277085 6570894102850902605728907)
      ·
        refine ⟨9856341154276353908593361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6570894102850902605728907 9856341154276353908593361)
        ·
          refine ⟨7392255865707265431445021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9856341154276353908593361 7392255865707265431445021)
          ·
            refine ⟨2772095949640224536791883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7392255865707265431445021 2772095949640224536791883)
            ·
              refine ⟨4158143924460336805187825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772095949640224536791883 4158143924460336805187825)
              ·
                refine ⟨3118607943345252603890869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158143924460336805187825 3118607943345252603890869)
                ·
                  refine ⟨292369494688617431614769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3118607943345252603890869 292369494688617431614769)
                  ·
                    rfl

theorem cell22_2562244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_2562244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562244 prefixEnd_2562244 := by exact prefixLift 2562244
  have htrace : WordTrace (prefixWord ++ tailWord_2562244) baseStart_2562244 baseEnd_2562244 := by
    simpa [prefixWord, tailWord_2562244, baseEnd_2562244] using wordTrace_append hprefix tailTrace_2562244
  have hstable : (prefixWord ++ tailWord_2562244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562244).length < 2 ^ (prefixWord ++ tailWord_2562244).sum := by decide
  have hdescent : baseEnd_2562244 < baseStart_2562244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562255 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 6]
def baseStart_2562255 : Nat := 118140960795 + 2562255 * 2 ^ 59
def prefixEnd_2562255 : Nat := 4983230072969 + 3 ^ 40 * 2562255 * 2
def baseEnd_2562255 : Nat := 292370749863550644273091

theorem tailTrace_2562255 : CollatzResearch.WordTrace tailWord_2562255 prefixEnd_2562255 292370749863550644273091 := by
  unfold tailWord_2562255
  simp only [CollatzResearch.WordTrace]
  refine ⟨93453117332395208160128219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62302078221596805440085479 93453117332395208160128219)
  ·
    refine ⟨140179675998592812240192329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93453117332395208160128219 140179675998592812240192329)
    ·
      refine ⟨105134756998944609180144247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140179675998592812240192329 105134756998944609180144247)
      ·
        refine ⟨157702135498416913770216371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105134756998944609180144247 157702135498416913770216371)
        ·
          refine ⟨236553203247625370655324557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157702135498416913770216371 236553203247625370655324557)
          ·
            refine ⟨88707451217859513995746709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236553203247625370655324557 88707451217859513995746709)
            ·
              refine ⟨4158161775837164718550627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88707451217859513995746709 4158161775837164718550627)
              ·
                refine ⟨6237242663755747077825941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158161775837164718550627 6237242663755747077825941)
                ·
                  refine ⟨292370749863550644273091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6237242663755747077825941 292370749863550644273091)
                  ·
                    rfl

theorem cell22_2562255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 6].length) (baseStart_2562255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562255 prefixEnd_2562255 := by exact prefixLift 2562255
  have htrace : WordTrace (prefixWord ++ tailWord_2562255) baseStart_2562255 baseEnd_2562255 := by
    simpa [prefixWord, tailWord_2562255, baseEnd_2562255] using wordTrace_append hprefix tailTrace_2562255
  have hstable : (prefixWord ++ tailWord_2562255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562255).length < 2 ^ (prefixWord ++ tailWord_2562255).sum := by decide
  have hdescent : baseEnd_2562255 < baseStart_2562255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562287 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 4, 3]
def baseStart_2562287 : Nat := 118140960795 + 2562287 * 2 ^ 59
def prefixEnd_2562287 : Nat := 4983230072969 + 3 ^ 40 * 2562287 * 2
def baseEnd_2562287 : Nat := 877123203844614516019175

theorem tailTrace_2562287 : CollatzResearch.WordTrace tailWord_2562287 prefixEnd_2562287 877123203844614516019175 := by
  unfold tailWord_2562287
  simp only [CollatzResearch.WordTrace]
  refine ⟨93454284468279277625293115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62302856312186185083528743 93454284468279277625293115)
  ·
    refine ⟨140181426702418916437939673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93454284468279277625293115 140181426702418916437939673)
    ·
      refine ⟨105136070026814187328454755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140181426702418916437939673 105136070026814187328454755)
      ·
        refine ⟨157704105040221280992682133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105136070026814187328454755 157704105040221280992682133)
        ·
          refine ⟨7392379923760372546531975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157704105040221280992682133 7392379923760372546531975)
          ·
            refine ⟨11088569885640558819797963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392379923760372546531975 11088569885640558819797963)
            ·
              refine ⟨16632854828460838229696945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11088569885640558819797963 16632854828460838229696945)
              ·
                refine ⟨12474641121345628672272709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16632854828460838229696945 12474641121345628672272709)
                ·
                  refine ⟨2338995210252305376051133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12474641121345628672272709 2338995210252305376051133)
                  ·
                    refine ⟨877123203844614516019175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338995210252305376051133 877123203844614516019175)
                    ·
                      rfl

theorem cell22_2562287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_2562287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562287 prefixEnd_2562287 := by exact prefixLift 2562287
  have htrace : WordTrace (prefixWord ++ tailWord_2562287) baseStart_2562287 baseEnd_2562287 := by
    simpa [prefixWord, tailWord_2562287, baseEnd_2562287] using wordTrace_append hprefix tailTrace_2562287
  have hstable : (prefixWord ++ tailWord_2562287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562287).length < 2 ^ (prefixWord ++ tailWord_2562287).sum := by decide
  have hdescent : baseEnd_2562287 < baseStart_2562287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562300 : List Nat := [2, 2, 2, 1, 4, 1, 10]
def baseStart_2562300 : Nat := 118140960795 + 2562300 * 2 ^ 59
def prefixEnd_2562300 : Nat := 4983230072969 + 3 ^ 40 * 2562300 * 2
def baseEnd_2562300 : Nat := 32486209407788400572005

theorem tailTrace_2562300 : CollatzResearch.WordTrace tailWord_2562300 prefixEnd_2562300 32486209407788400572005 := by
  unfold tailWord_2562300
  simp only [CollatzResearch.WordTrace]
  refine ⟨46727379308616090422758177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62303172411488120563677569 46727379308616090422758177)
  ·
    refine ⟨35045534481462067817068633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46727379308616090422758177 35045534481462067817068633)
    ·
      refine ⟨26284150861096550862801475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35045534481462067817068633 26284150861096550862801475)
      ·
        refine ⟨39426226291644826294202213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26284150861096550862801475 39426226291644826294202213)
        ·
          refine ⟨7392417429683404930162915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39426226291644826294202213 7392417429683404930162915)
          ·
            refine ⟨11088626144525107395244373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392417429683404930162915 11088626144525107395244373)
            ·
              refine ⟨32486209407788400572005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11088626144525107395244373 32486209407788400572005)
              ·
                rfl

theorem cell22_2562300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 10].length) (baseStart_2562300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562300 prefixEnd_2562300 := by exact prefixLift 2562300
  have htrace : WordTrace (prefixWord ++ tailWord_2562300) baseStart_2562300 baseEnd_2562300 := by
    simpa [prefixWord, tailWord_2562300, baseEnd_2562300] using wordTrace_append hprefix tailTrace_2562300
  have hstable : (prefixWord ++ tailWord_2562300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562300).length < 2 ^ (prefixWord ++ tailWord_2562300).sum := by decide
  have hdescent : baseEnd_2562300 < baseStart_2562300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562321 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 2, 3]
def baseStart_2562321 : Nat := 118140960795 + 2562321 * 2 ^ 59
def prefixEnd_2562321 : Nat := 4983230072969 + 3 ^ 40 * 2562321 * 2
def baseEnd_2562321 : Nat := 877134842739449760669071

theorem tailTrace_2562321 : CollatzResearch.WordTrace tailWord_2562321 prefixEnd_2562321 877134842739449760669071 := by
  unfold tailWord_2562321
  simp only [CollatzResearch.WordTrace]
  refine ⟨93455524550156101432030817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62303683033437400954687211 93455524550156101432030817)
  ·
    refine ⟨70091643412617076074023113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93455524550156101432030817 70091643412617076074023113)
    ·
      refine ⟨52568732559462807055517335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70091643412617076074023113 52568732559462807055517335)
      ·
        refine ⟨78853098839194210583276003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52568732559462807055517335 78853098839194210583276003)
        ·
          refine ⟨118279648258791315874914005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78853098839194210583276003 118279648258791315874914005)
          ·
            refine ⟨2772179256065421465818297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118279648258791315874914005 2772179256065421465818297)
            ·
              refine ⟨2079134442049066099363723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772179256065421465818297 2079134442049066099363723)
              ·
                refine ⟨3118701663073599149045585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079134442049066099363723 3118701663073599149045585)
                ·
                  refine ⟨2339026247305199361784189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3118701663073599149045585 2339026247305199361784189)
                  ·
                    refine ⟨877134842739449760669071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2339026247305199361784189 877134842739449760669071)
                    ·
                      rfl

theorem cell22_2562321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_2562321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562321 prefixEnd_2562321 := by exact prefixLift 2562321
  have htrace : WordTrace (prefixWord ++ tailWord_2562321) baseStart_2562321 baseEnd_2562321 := by
    simpa [prefixWord, tailWord_2562321, baseEnd_2562321] using wordTrace_append hprefix tailTrace_2562321
  have hstable : (prefixWord ++ tailWord_2562321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562321).length < 2 ^ (prefixWord ++ tailWord_2562321).sum := by decide
  have hdescent : baseEnd_2562321 < baseStart_2562321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562332 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2562332 : Nat := 118140960795 + 2562332 * 2 ^ 59
def prefixEnd_2562332 : Nat := 4983230072969 + 3 ^ 40 * 2562332 * 2
def baseEnd_2562332 : Nat := 877138608264249398644037

theorem tailTrace_2562332 : CollatzResearch.WordTrace tailWord_2562332 prefixEnd_2562332 877138608264249398644037 := by
  unfold tailWord_2562332
  simp only [CollatzResearch.WordTrace]
  refine ⟨46727962876558125155340625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62303950502077500207120833 46727962876558125155340625)
  ·
    refine ⟨35045972157418593866505469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46727962876558125155340625 35045972157418593866505469)
    ·
      refine ⟨13142239559031972699939551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35045972157418593866505469 13142239559031972699939551)
      ·
        refine ⟨19713359338547959049909327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13142239559031972699939551 19713359338547959049909327)
        ·
          refine ⟨29570039007821938574863991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19713359338547959049909327 29570039007821938574863991)
          ·
            refine ⟨44355058511732907862295987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29570039007821938574863991 44355058511732907862295987)
            ·
              refine ⟨66532587767599361793443981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44355058511732907862295987 66532587767599361793443981)
              ·
                refine ⟨24949720412849760672541493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66532587767599361793443981 24949720412849760672541493)
                ·
                  refine ⟨2339036288704665063050765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24949720412849760672541493 2339036288704665063050765)
                  ·
                    refine ⟨877138608264249398644037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2339036288704665063050765 877138608264249398644037)
                    ·
                      rfl

theorem cell22_2562332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2562332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562332 prefixEnd_2562332 := by exact prefixLift 2562332
  have htrace : WordTrace (prefixWord ++ tailWord_2562332) baseStart_2562332 baseEnd_2562332 := by
    simpa [prefixWord, tailWord_2562332, baseEnd_2562332] using wordTrace_append hprefix tailTrace_2562332
  have hstable : (prefixWord ++ tailWord_2562332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562332).length < 2 ^ (prefixWord ++ tailWord_2562332).sum := by decide
  have hdescent : baseEnd_2562332 < baseStart_2562332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562334 : List Nat := [4, 3, 2, 1, 1, 1, 2, 8]
def baseStart_2562334 : Nat := 118140960795 + 2562334 * 2 ^ 59
def prefixEnd_2562334 : Nat := 4983230072969 + 3 ^ 40 * 2562334 * 2
def baseEnd_2562334 : Nat := 97459921433902451121559

theorem tailTrace_2562334 : CollatzResearch.WordTrace tailWord_2562334 prefixEnd_2562334 97459921433902451121559 := by
  unfold tailWord_2562334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11681999837388625581531757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62303999132739336434836037 11681999837388625581531757)
  ·
    refine ⟨4380749939020734593074409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11681999837388625581531757 4380749939020734593074409)
    ·
      refine ⟨3285562454265550944805807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4380749939020734593074409 3285562454265550944805807)
      ·
        refine ⟨4928343681398326417208711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285562454265550944805807 4928343681398326417208711)
        ·
          refine ⟨7392515522097489625813067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4928343681398326417208711 7392515522097489625813067)
          ·
            refine ⟨11088773283146234438719601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392515522097489625813067 11088773283146234438719601)
            ·
              refine ⟨8316579962359675829039701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11088773283146234438719601 8316579962359675829039701)
              ·
                refine ⟨97459921433902451121559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8316579962359675829039701 97459921433902451121559)
                ·
                  rfl

theorem cell22_2562334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_2562334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562334 prefixEnd_2562334 := by exact prefixLift 2562334
  have htrace : WordTrace (prefixWord ++ tailWord_2562334) baseStart_2562334 baseEnd_2562334 := by
    simpa [prefixWord, tailWord_2562334, baseEnd_2562334] using wordTrace_append hprefix tailTrace_2562334
  have hstable : (prefixWord ++ tailWord_2562334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562334).length < 2 ^ (prefixWord ++ tailWord_2562334).sum := by decide
  have hdescent : baseEnd_2562334 < baseStart_2562334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562362 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_2562362 : Nat := 118140960795 + 2562362 * 2 ^ 59
def prefixEnd_2562362 : Nat := 4983230072969 + 3 ^ 40 * 2562362 * 2
def baseEnd_2562362 : Nat := 292382959292446440131315

theorem tailTrace_2562362 : CollatzResearch.WordTrace tailWord_2562362 prefixEnd_2562362 292382959292446440131315 := by
  unfold tailWord_2562362
  simp only [CollatzResearch.WordTrace]
  refine ⟨23364254985751891358568335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62304679962005043622848893 23364254985751891358568335)
  ·
    refine ⟨35046382478627837037852503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23364254985751891358568335 35046382478627837037852503)
    ·
      refine ⟨52569573717941755556778755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35046382478627837037852503 52569573717941755556778755)
      ·
        refine ⟨78854360576912633335168133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52569573717941755556778755 78854360576912633335168133)
        ·
          refine ⟨14785192608171118750344025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78854360576912633335168133 14785192608171118750344025)
          ·
            refine ⟨11088894456128339062758019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14785192608171118750344025 11088894456128339062758019)
            ·
              refine ⟨16633341684192508594137029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11088894456128339062758019 16633341684192508594137029)
              ·
                refine ⟨3118751565786095361400693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16633341684192508594137029 3118751565786095361400693)
                ·
                  refine ⟨292382959292446440131315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3118751565786095361400693 292382959292446440131315)
                  ·
                    rfl

theorem cell22_2562362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_2562362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562362 prefixEnd_2562362 := by exact prefixLift 2562362
  have htrace : WordTrace (prefixWord ++ tailWord_2562362) baseStart_2562362 baseEnd_2562362 := by
    simpa [prefixWord, tailWord_2562362, baseEnd_2562362] using wordTrace_append hprefix tailTrace_2562362
  have hstable : (prefixWord ++ tailWord_2562362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562362).length < 2 ^ (prefixWord ++ tailWord_2562362).sum := by decide
  have hdescent : baseEnd_2562362 < baseStart_2562362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562482 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2562482 : Nat := 118140960795 + 2562482 * 2 ^ 59
def prefixEnd_2562482 : Nat := 4983230072969 + 3 ^ 40 * 2562482 * 2
def baseEnd_2562482 : Nat := 877189956329699007393577

theorem tailTrace_2562482 : CollatzResearch.WordTrace tailWord_2562482 prefixEnd_2562482 877189956329699007393577 := by
  unfold tailWord_2562482
  simp only [CollatzResearch.WordTrace]
  refine ⟨23365349175643206482160425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62307597801715217285761133 23365349175643206482160425)
  ·
    refine ⟨17524011881732404861620319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23365349175643206482160425 17524011881732404861620319)
    ·
      refine ⟨26286017822598607292430479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17524011881732404861620319 26286017822598607292430479)
      ·
        refine ⟨39429026733897910938645719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26286017822598607292430479 39429026733897910938645719)
        ·
          refine ⟨59143540100846866407968579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39429026733897910938645719 59143540100846866407968579)
          ·
            refine ⟨88715310151270299611952869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59143540100846866407968579 88715310151270299611952869)
            ·
              refine ⟨16634120653363181177241163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88715310151270299611952869 16634120653363181177241163)
              ·
                refine ⟨24951180980044771765861745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16634120653363181177241163 24951180980044771765861745)
                ·
                  refine ⟨18713385735033578824396309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24951180980044771765861745 18713385735033578824396309)
                  ·
                    refine ⟨877189956329699007393577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18713385735033578824396309 877189956329699007393577)
                    ·
                      rfl

theorem cell22_2562482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2562482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562482 prefixEnd_2562482 := by exact prefixLift 2562482
  have htrace : WordTrace (prefixWord ++ tailWord_2562482) baseStart_2562482 baseEnd_2562482 := by
    simpa [prefixWord, tailWord_2562482, baseEnd_2562482] using wordTrace_append hprefix tailTrace_2562482
  have hstable : (prefixWord ++ tailWord_2562482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562482).length < 2 ^ (prefixWord ++ tailWord_2562482).sum := by decide
  have hdescent : baseEnd_2562482 < baseStart_2562482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562531 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 5]
def baseStart_2562531 : Nat := 118140960795 + 2562531 * 2 ^ 59
def prefixEnd_2562531 : Nat := 4983230072969 + 3 ^ 40 * 2562531 * 2
def baseEnd_2562531 : Nat := 292402243343693070972809

theorem tailTrace_2562531 : CollatzResearch.WordTrace tailWord_2562531 prefixEnd_2562531 292402243343693070972809 := by
  unfold tailWord_2562531
  simp only [CollatzResearch.WordTrace]
  refine ⟨93463183879395307297175447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62308789252930204864783631 93463183879395307297175447)
  ·
    refine ⟨140194775819092960945763171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93463183879395307297175447 140194775819092960945763171)
    ·
      refine ⟨210292163728639441418644757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140194775819092960945763171 210292163728639441418644757)
      ·
        refine ⟨9857445174779973816498973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 210292163728639441418644757 9857445174779973816498973)
        ·
          refine ⟨3696541940542490181187115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9857445174779973816498973 3696541940542490181187115)
          ·
            refine ⟨5544812910813735271780673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696541940542490181187115 5544812910813735271780673)
            ·
              refine ⟨4158609683110301453835505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5544812910813735271780673 4158609683110301453835505)
              ·
                refine ⟨3118957262332726090376629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158609683110301453835505 3118957262332726090376629)
                ·
                  refine ⟨292402243343693070972809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3118957262332726090376629 292402243343693070972809)
                  ·
                    rfl

theorem cell22_2562531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 5].length) (baseStart_2562531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562531 prefixEnd_2562531 := by exact prefixLift 2562531
  have htrace : WordTrace (prefixWord ++ tailWord_2562531) baseStart_2562531 baseEnd_2562531 := by
    simpa [prefixWord, tailWord_2562531, baseEnd_2562531] using wordTrace_append hprefix tailTrace_2562531
  have hstable : (prefixWord ++ tailWord_2562531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562531).length < 2 ^ (prefixWord ++ tailWord_2562531).sum := by decide
  have hdescent : baseEnd_2562531 < baseStart_2562531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562546 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_2562546 : Nat := 118140960795 + 2562546 * 2 ^ 59
def prefixEnd_2562546 : Nat := 4983230072969 + 3 ^ 40 * 2562546 * 2
def baseEnd_2562546 : Nat := 877211864837624173793381

theorem tailTrace_2562546 : CollatzResearch.WordTrace tailWord_2562546 prefixEnd_2562546 877211864837624173793381 := by
  unfold tailWord_2562546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23365932743585241214742873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62309153982893976572647661 23365932743585241214742873)
  ·
    refine ⟨17524449557688930911057155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23365932743585241214742873 17524449557688930911057155)
    ·
      refine ⟨26286674336533396366585733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17524449557688930911057155 26286674336533396366585733)
      ·
        refine ⟨4928751438100011818734825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26286674336533396366585733 4928751438100011818734825)
        ·
          refine ⟨3696563578575008864051119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4928751438100011818734825 3696563578575008864051119)
          ·
            refine ⟨5544845367862513296076679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696563578575008864051119 5544845367862513296076679)
            ·
              refine ⟨8317268051793769944115019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5544845367862513296076679 8317268051793769944115019)
              ·
                refine ⟨12475902077690654916172529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8317268051793769944115019 12475902077690654916172529)
                ·
                  refine ⟨9356926558267991187129397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12475902077690654916172529 9356926558267991187129397)
                  ·
                    refine ⟨877211864837624173793381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9356926558267991187129397 877211864837624173793381)
                    ·
                      rfl

theorem cell22_2562546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_2562546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562546 prefixEnd_2562546 := by exact prefixLift 2562546
  have htrace : WordTrace (prefixWord ++ tailWord_2562546) baseStart_2562546 baseEnd_2562546 := by
    simpa [prefixWord, tailWord_2562546, baseEnd_2562546] using wordTrace_append hprefix tailTrace_2562546
  have hstable : (prefixWord ++ tailWord_2562546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562546).length < 2 ^ (prefixWord ++ tailWord_2562546).sum := by decide
  have hdescent : baseEnd_2562546 < baseStart_2562546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562619 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 9, 3]
def baseStart_2562619 : Nat := 118140960795 + 2562619 * 2 ^ 59
def prefixEnd_2562619 : Nat := 4983230072969 + 3 ^ 40 * 2562619 * 2
def baseEnd_2562619 : Nat := 877236854229476316718157

theorem tailTrace_2562619 : CollatzResearch.WordTrace tailWord_2562619 prefixEnd_2562619 877236854229476316718157 := by
  unfold tailWord_2562619
  simp only [CollatzResearch.WordTrace]
  refine ⟨93466393503076498326378911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62310929002050998884252607 93466393503076498326378911)
  ·
    refine ⟨140199590254614747489568367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93466393503076498326378911 140199590254614747489568367)
    ·
      refine ⟨210299385381922121234352551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140199590254614747489568367 210299385381922121234352551)
      ·
        refine ⟨315449078072883181851528827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210299385381922121234352551 315449078072883181851528827)
        ·
          refine ⟨473173617109324772777293241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315449078072883181851528827 473173617109324772777293241)
          ·
            refine ⟨354880212831993579582969931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473173617109324772777293241 354880212831993579582969931)
            ·
              refine ⟨532320319247990369374454897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354880212831993579582969931 532320319247990369374454897)
              ·
                refine ⟨399240239435992777030841173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532320319247990369374454897 399240239435992777030841173)
                ·
                  refine ⟨2339298277945270177915085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 399240239435992777030841173 2339298277945270177915085)
                  ·
                    refine ⟨877236854229476316718157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2339298277945270177915085 877236854229476316718157)
                    ·
                      rfl

theorem cell22_2562619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 3].length) (baseStart_2562619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562619 prefixEnd_2562619 := by exact prefixLift 2562619
  have htrace : WordTrace (prefixWord ++ tailWord_2562619) baseStart_2562619 baseEnd_2562619 := by
    simpa [prefixWord, tailWord_2562619, baseEnd_2562619] using wordTrace_append hprefix tailTrace_2562619
  have hstable : (prefixWord ++ tailWord_2562619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562619).length < 2 ^ (prefixWord ++ tailWord_2562619).sum := by decide
  have hdescent : baseEnd_2562619 < baseStart_2562619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562621 : List Nat := [1, 4, 1, 3, 2, 1, 4, 6]
def baseStart_2562621 : Nat := 118140960795 + 2562621 * 2 ^ 59
def prefixEnd_2562621 : Nat := 4983230072969 + 3 ^ 40 * 2562621 * 2
def baseEnd_2562621 : Nat := 97470837652260997574239

theorem tailTrace_2562621 : CollatzResearch.WordTrace tailWord_2562621 prefixEnd_2562621 97470837652260997574239 := by
  unfold tailWord_2562621
  simp only [CollatzResearch.WordTrace]
  refine ⟨93466466449069252667951717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62310977632712835111967811 93466466449069252667951717)
  ·
    refine ⟨17524962459200484875240947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93466466449069252667951717 17524962459200484875240947)
    ·
      refine ⟨26287443688800727312861421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17524962459200484875240947 26287443688800727312861421)
      ·
        refine ⟨9857791383300272742323033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26287443688800727312861421 9857791383300272742323033)
        ·
          refine ⟨7393343537475204556742275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9857791383300272742323033 7393343537475204556742275)
          ·
            refine ⟨11090015306212806835113413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393343537475204556742275 11090015306212806835113413)
            ·
              refine ⟨2079377869914901281583765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11090015306212806835113413 2079377869914901281583765)
              ·
                refine ⟨97470837652260997574239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2079377869914901281583765 97470837652260997574239)
                ·
                  rfl

theorem cell22_2562621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 6].length) (baseStart_2562621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562621 prefixEnd_2562621 := by exact prefixLift 2562621
  have htrace : WordTrace (prefixWord ++ tailWord_2562621) baseStart_2562621 baseEnd_2562621 := by
    simpa [prefixWord, tailWord_2562621, baseEnd_2562621] using wordTrace_append hprefix tailTrace_2562621
  have hstable : (prefixWord ++ tailWord_2562621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562621).length < 2 ^ (prefixWord ++ tailWord_2562621).sum := by decide
  have hdescent : baseEnd_2562621 < baseStart_2562621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562666 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_2562666 : Nat := 118140960795 + 2562666 * 2 ^ 59
def prefixEnd_2562666 : Nat := 4983230072969 + 3 ^ 40 * 2562666 * 2
def baseEnd_2562666 : Nat := 292417647763327953597671

theorem tailTrace_2562666 : CollatzResearch.WordTrace tailWord_2562666 prefixEnd_2562666 292417647763327953597671 := by
  unfold tailWord_2562666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23367026933476556338334963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62312071822604150235559901 23367026933476556338334963)
  ·
    refine ⟨35050540400214834507502445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23367026933476556338334963 35050540400214834507502445)
    ·
      refine ⟨13143952650080562940313417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35050540400214834507502445 13143952650080562940313417)
      ·
        refine ⟨9857964487560422205235063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13143952650080562940313417 9857964487560422205235063)
        ·
          refine ⟨14786946731340633307852595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857964487560422205235063 14786946731340633307852595)
          ·
            refine ⟨22180420097010949961778893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14786946731340633307852595 22180420097010949961778893)
            ·
              refine ⟨8317657536379106235667085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22180420097010949961778893 8317657536379106235667085)
              ·
                refine ⟨3119121576142164838375157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8317657536379106235667085 3119121576142164838375157)
                ·
                  refine ⟨292417647763327953597671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3119121576142164838375157 292417647763327953597671)
                  ·
                    rfl

theorem cell22_2562666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_2562666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562666 prefixEnd_2562666 := by exact prefixLift 2562666
  have htrace : WordTrace (prefixWord ++ tailWord_2562666) baseStart_2562666 baseEnd_2562666 := by
    simpa [prefixWord, tailWord_2562666, baseEnd_2562666] using wordTrace_append hprefix tailTrace_2562666
  have hstable : (prefixWord ++ tailWord_2562666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562666).length < 2 ^ (prefixWord ++ tailWord_2562666).sum := by decide
  have hdescent : baseEnd_2562666 < baseStart_2562666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562756 : List Nat := [2, 3, 3, 1, 1, 3, 9]
def baseStart_2562756 : Nat := 118140960795 + 2562756 * 2 ^ 59
def prefixEnd_2562756 : Nat := 4983230072969 + 3 ^ 40 * 2562756 * 2
def baseEnd_2562756 : Nat := 32491990819601986149731

theorem tailTrace_2562756 : CollatzResearch.WordTrace tailWord_2562756 prefixEnd_2562756 32491990819601986149731 := by
  unfold tailWord_2562756
  simp only [CollatzResearch.WordTrace]
  refine ⟨46735695151790085362058061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62314260202386780482744081 46735695151790085362058061)
  ·
    refine ⟨17525885681921282010771773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46735695151790085362058061 17525885681921282010771773)
    ·
      refine ⟨6572207130720480754039415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17525885681921282010771773 6572207130720480754039415)
      ·
        refine ⟨9858310696080721131059123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6572207130720480754039415 9858310696080721131059123)
        ·
          refine ⟨14787466044121081696588685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9858310696080721131059123 14787466044121081696588685)
          ·
            refine ⟨5545299766545405636220757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14787466044121081696588685 5545299766545405636220757)
            ·
              refine ⟨32491990819601986149731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5545299766545405636220757 32491990819601986149731)
              ·
                rfl

theorem cell22_2562756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 9].length) (baseStart_2562756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562756 prefixEnd_2562756 := by exact prefixLift 2562756
  have htrace : WordTrace (prefixWord ++ tailWord_2562756) baseStart_2562756 baseEnd_2562756 := by
    simpa [prefixWord, tailWord_2562756, baseEnd_2562756] using wordTrace_append hprefix tailTrace_2562756
  have hstable : (prefixWord ++ tailWord_2562756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562756).length < 2 ^ (prefixWord ++ tailWord_2562756).sum := by decide
  have hdescent : baseEnd_2562756 < baseStart_2562756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562760 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 2, 3]
def baseStart_2562760 : Nat := 118140960795 + 2562760 * 2 ^ 59
def prefixEnd_2562760 : Nat := 4983230072969 + 3 ^ 40 * 2562760 * 2
def baseEnd_2562760 : Nat := 877285121410998948942725

theorem tailTrace_2562760 : CollatzResearch.WordTrace tailWord_2562760 prefixEnd_2562760 877285121410998948942725 := by
  unfold tailWord_2562760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46735768097782839703630867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62314357463710452938174489 46735768097782839703630867)
  ·
    refine ⟨70103652146674259555446301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46735768097782839703630867 70103652146674259555446301)
    ·
      refine ⟨26288869555002847333292363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70103652146674259555446301 26288869555002847333292363)
      ·
        refine ⟨39433304332504270999938545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26288869555002847333292363 39433304332504270999938545)
        ·
          refine ⟨29574978249378203249953909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39433304332504270999938545 29574978249378203249953909)
          ·
            refine ⟨2772654210879206554683179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29574978249378203249953909 2772654210879206554683179)
            ·
              refine ⟨4158981316318809832024769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772654210879206554683179 4158981316318809832024769)
              ·
                refine ⟨3119235987239107374018577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158981316318809832024769 3119235987239107374018577)
                ·
                  refine ⟨2339426990429330530513933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3119235987239107374018577 2339426990429330530513933)
                  ·
                    refine ⟨877285121410998948942725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2339426990429330530513933 877285121410998948942725)
                    ·
                      rfl

theorem cell22_2562760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_2562760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562760 prefixEnd_2562760 := by exact prefixLift 2562760
  have htrace : WordTrace (prefixWord ++ tailWord_2562760) baseStart_2562760 baseEnd_2562760 := by
    simpa [prefixWord, tailWord_2562760, baseEnd_2562760] using wordTrace_append hprefix tailTrace_2562760
  have hstable : (prefixWord ++ tailWord_2562760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562760).length < 2 ^ (prefixWord ++ tailWord_2562760).sum := by decide
  have hdescent : baseEnd_2562760 < baseStart_2562760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562788 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_2562788 : Nat := 118140960795 + 2562788 * 2 ^ 59
def prefixEnd_2562788 : Nat := 4983230072969 + 3 ^ 40 * 2562788 * 2
def baseEnd_2562788 : Nat := 877294706383216209242639

theorem tailTrace_2562788 : CollatzResearch.WordTrace tailWord_2562788 prefixEnd_2562788 877294706383216209242639 := by
  unfold tailWord_2562788
  simp only [CollatzResearch.WordTrace]
  refine ⟨46736278719732120094640509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62315038292976160126187345 46736278719732120094640509)
  ·
    refine ⟨17526104519899545035490191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46736278719732120094640509 17526104519899545035490191)
    ·
      refine ⟨26289156779849317553235287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17526104519899545035490191 26289156779849317553235287)
      ·
        refine ⟨39433735169773976329852931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26289156779849317553235287 39433735169773976329852931)
        ·
          refine ⟨59150602754660964494779397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39433735169773976329852931 59150602754660964494779397)
          ·
            refine ⟨11090738016498930842771137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59150602754660964494779397 11090738016498930842771137)
            ·
              refine ⟨8318053512374198132078353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11090738016498930842771137 8318053512374198132078353)
              ·
                refine ⟨6238540134280648599058765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8318053512374198132078353 6238540134280648599058765)
                ·
                  refine ⟨2339452550355243224647037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6238540134280648599058765 2339452550355243224647037)
                  ·
                    refine ⟨877294706383216209242639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2339452550355243224647037 877294706383216209242639)
                    ·
                      rfl

theorem cell22_2562788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_2562788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562788 prefixEnd_2562788 := by exact prefixLift 2562788
  have htrace : WordTrace (prefixWord ++ tailWord_2562788) baseStart_2562788 baseEnd_2562788 := by
    simpa [prefixWord, tailWord_2562788, baseEnd_2562788] using wordTrace_append hprefix tailTrace_2562788
  have hstable : (prefixWord ++ tailWord_2562788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562788).length < 2 ^ (prefixWord ++ tailWord_2562788).sum := by decide
  have hdescent : baseEnd_2562788 < baseStart_2562788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562818 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2562818 : Nat := 118140960795 + 2562818 * 2 ^ 59
def prefixEnd_2562818 : Nat := 4983230072969 + 3 ^ 40 * 2562818 * 2
def baseEnd_2562818 : Nat := 292434991998768710330849

theorem tailTrace_2562818 : CollatzResearch.WordTrace tailWord_2562818 prefixEnd_2562818 292434991998768710330849 := by
  unfold tailWord_2562818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23368412907338888828218277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62315767752903703541915405 23368412907338888828218277)
  ·
    refine ⟨4381577420126041655290927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23368412907338888828218277 4381577420126041655290927)
    ·
      refine ⟨6572366130189062482936391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4381577420126041655290927 6572366130189062482936391)
      ·
        refine ⟨9858549195283593724404587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6572366130189062482936391 9858549195283593724404587)
        ·
          refine ⟨14787823792925390586606881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9858549195283593724404587 14787823792925390586606881)
          ·
            refine ⟨11090867844694042939955161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14787823792925390586606881 11090867844694042939955161)
            ·
              refine ⟨8318150883520532204966371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11090867844694042939955161 8318150883520532204966371)
              ·
                refine ⟨12477226325280798307449557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8318150883520532204966371 12477226325280798307449557)
                ·
                  refine ⟨292434991998768710330849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12477226325280798307449557 292434991998768710330849)
                  ·
                    rfl

theorem cell22_2562818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2562818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562818 prefixEnd_2562818 := by exact prefixLift 2562818
  have htrace : WordTrace (prefixWord ++ tailWord_2562818) baseStart_2562818 baseEnd_2562818 := by
    simpa [prefixWord, tailWord_2562818, baseEnd_2562818] using wordTrace_append hprefix tailTrace_2562818
  have hstable : (prefixWord ++ tailWord_2562818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562818).length < 2 ^ (prefixWord ++ tailWord_2562818).sum := by decide
  have hdescent : baseEnd_2562818 < baseStart_2562818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562831 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 3, 4]
def baseStart_2562831 : Nat := 118140960795 + 2562831 * 2 ^ 59
def prefixEnd_2562831 : Nat := 4983230072969 + 3 ^ 40 * 2562831 * 2
def baseEnd_2562831 : Nat := 877309426161978430417507

theorem tailTrace_2562831 : CollatzResearch.WordTrace tailWord_2562831 prefixEnd_2562831 877309426161978430417507 := by
  unfold tailWord_2562831
  simp only [CollatzResearch.WordTrace]
  refine ⟨93474125778308458533096347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62316083852205639022064231 93474125778308458533096347)
  ·
    refine ⟨140211188667462687799644521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93474125778308458533096347 140211188667462687799644521)
    ·
      refine ⟨105158391500597015849733391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140211188667462687799644521 105158391500597015849733391)
      ·
        refine ⟨157737587250895523774600087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105158391500597015849733391 157737587250895523774600087)
        ·
          refine ⟨236606380876343285661900131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157737587250895523774600087 236606380876343285661900131)
          ·
            refine ⟨354909571314514928492850197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236606380876343285661900131 354909571314514928492850197)
            ·
              refine ⟨16636386155367887273102353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 354909571314514928492850197 16636386155367887273102353)
              ·
                refine ⟨12477289616525915454826765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16636386155367887273102353 12477289616525915454826765)
                ·
                  refine ⟨4678983606197218295560037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12477289616525915454826765 4678983606197218295560037)
                  ·
                    refine ⟨877309426161978430417507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4678983606197218295560037 877309426161978430417507)
                    ·
                      rfl

theorem cell22_2562831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_2562831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562831 prefixEnd_2562831 := by exact prefixLift 2562831
  have htrace : WordTrace (prefixWord ++ tailWord_2562831) baseStart_2562831 baseEnd_2562831 := by
    simpa [prefixWord, tailWord_2562831, baseEnd_2562831] using wordTrace_append hprefix tailTrace_2562831
  have hstable : (prefixWord ++ tailWord_2562831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562831).length < 2 ^ (prefixWord ++ tailWord_2562831).sum := by decide
  have hdescent : baseEnd_2562831 < baseStart_2562831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562848 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_2562848 : Nat := 118140960795 + 2562848 * 2 ^ 59
def prefixEnd_2562848 : Nat := 4983230072969 + 3 ^ 40 * 2562848 * 2
def baseEnd_2562848 : Nat := 877315245609396052742455

theorem tailTrace_2562848 : CollatzResearch.WordTrace tailWord_2562848 prefixEnd_2562848 877315245609396052742455 := by
  unfold tailWord_2562848
  simp only [CollatzResearch.WordTrace]
  refine ⟨46737372909623435218232599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62316497212831246957643465 46737372909623435218232599)
  ·
    refine ⟨70106059364435152827348899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46737372909623435218232599 70106059364435152827348899)
    ·
      refine ⟨105159089046652729241023349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70106059364435152827348899 105159089046652729241023349)
      ·
        refine ⟨9858664598123693366345939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105159089046652729241023349 9858664598123693366345939)
        ·
          refine ⟨14787996897185540049518909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9858664598123693366345939 14787996897185540049518909)
          ·
            refine ⟨5545498836444577518569591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14787996897185540049518909 5545498836444577518569591)
            ·
              refine ⟨8318248254666866277854387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5545498836444577518569591 8318248254666866277854387)
              ·
                refine ⟨12477372382000299416781581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8318248254666866277854387 12477372382000299416781581)
                ·
                  refine ⟨4679014643250112281293093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12477372382000299416781581 4679014643250112281293093)
                  ·
                    refine ⟨877315245609396052742455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4679014643250112281293093 877315245609396052742455)
                    ·
                      rfl

theorem cell22_2562848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_2562848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562848 prefixEnd_2562848 := by exact prefixLift 2562848
  have htrace : WordTrace (prefixWord ++ tailWord_2562848) baseStart_2562848 baseEnd_2562848 := by
    simpa [prefixWord, tailWord_2562848, baseEnd_2562848] using wordTrace_append hprefix tailTrace_2562848
  have hstable : (prefixWord ++ tailWord_2562848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562848).length < 2 ^ (prefixWord ++ tailWord_2562848).sum := by decide
  have hdescent : baseEnd_2562848 < baseStart_2562848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562865 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 1, 4]
def baseStart_2562865 : Nat := 118140960795 + 2562865 * 2 ^ 59
def prefixEnd_2562865 : Nat := 4983230072969 + 3 ^ 40 * 2562865 * 2
def baseEnd_2562865 : Nat := 877321065056813675067403

theorem tailTrace_2562865 : CollatzResearch.WordTrace tailWord_2562865 prefixEnd_2562865 877321065056813675067403 := by
  unfold tailWord_2562865
  simp only [CollatzResearch.WordTrace]
  refine ⟨93475365860185282339834049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62316910573456854893222699 93475365860185282339834049)
  ·
    refine ⟨70106524395138961754875537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93475365860185282339834049 70106524395138961754875537)
    ·
      refine ⟨52579893296354221316156653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70106524395138961754875537 52579893296354221316156653)
      ·
        refine ⟨19717459986132832993558745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52579893296354221316156653 19717459986132832993558745)
        ·
          refine ⟨14788094989599624745169059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19717459986132832993558745 14788094989599624745169059)
          ·
            refine ⟨22182142484399437117753589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14788094989599624745169059 22182142484399437117753589)
            ·
              refine ⟨2079575857912447229789399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22182142484399437117753589 2079575857912447229789399)
              ·
                refine ⟨3119363786868670844684099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079575857912447229789399 3119363786868670844684099)
                ·
                  refine ⟨4679045680303006267026149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119363786868670844684099 4679045680303006267026149)
                  ·
                    refine ⟨877321065056813675067403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4679045680303006267026149 877321065056813675067403)
                    ·
                      rfl

theorem cell22_2562865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_2562865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562865 prefixEnd_2562865 := by exact prefixLift 2562865
  have htrace : WordTrace (prefixWord ++ tailWord_2562865) baseStart_2562865 baseEnd_2562865 := by
    simpa [prefixWord, tailWord_2562865, baseEnd_2562865] using wordTrace_append hprefix tailTrace_2562865
  have hstable : (prefixWord ++ tailWord_2562865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562865).length < 2 ^ (prefixWord ++ tailWord_2562865).sum := by decide
  have hdescent : baseEnd_2562865 < baseStart_2562865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562876 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2562876 : Nat := 118140960795 + 2562876 * 2 ^ 59
def prefixEnd_2562876 : Nat := 4983230072969 + 3 ^ 40 * 2562876 * 2
def baseEnd_2562876 : Nat := 877324830581613313042369

theorem tailTrace_2562876 : CollatzResearch.WordTrace tailWord_2562876 prefixEnd_2562876 877324830581613313042369 := by
  unfold tailWord_2562876
  simp only [CollatzResearch.WordTrace]
  refine ⟨46737883531572715609242241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62317178042096954145656321 46737883531572715609242241)
  ·
    refine ⟨35053412648679536706931681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46737883531572715609242241 35053412648679536706931681)
    ·
      refine ⟨26290059486509652530198761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35053412648679536706931681 26290059486509652530198761)
      ·
        refine ⟨19717544614882239397649071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26290059486509652530198761 19717544614882239397649071)
        ·
          refine ⟨29576316922323359096473607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19717544614882239397649071 29576316922323359096473607)
          ·
            refine ⟨44364475383485038644710411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29576316922323359096473607 44364475383485038644710411)
            ·
              refine ⟨66546713075227557967065617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44364475383485038644710411 66546713075227557967065617)
              ·
                refine ⟨49910034806420668475299213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66546713075227557967065617 49910034806420668475299213)
                ·
                  refine ⟨18716263052407750678237205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49910034806420668475299213 18716263052407750678237205)
                  ·
                    refine ⟨877324830581613313042369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18716263052407750678237205 877324830581613313042369)
                    ·
                      rfl

theorem cell22_2562876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2562876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562876 prefixEnd_2562876 := by exact prefixLift 2562876
  have htrace : WordTrace (prefixWord ++ tailWord_2562876) baseStart_2562876 baseEnd_2562876 := by
    simpa [prefixWord, tailWord_2562876, baseEnd_2562876] using wordTrace_append hprefix tailTrace_2562876
  have hstable : (prefixWord ++ tailWord_2562876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562876).length < 2 ^ (prefixWord ++ tailWord_2562876).sum := by decide
  have hdescent : baseEnd_2562876 < baseStart_2562876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2562946 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2562946 : Nat := 118140960795 + 2562946 * 2 ^ 59
def prefixEnd_2562946 : Nat := 4983230072969 + 3 ^ 40 * 2562946 * 2
def baseEnd_2562946 : Nat := 877348793012156463792155

theorem tailTrace_2562946 : CollatzResearch.WordTrace tailWord_2562946 prefixEnd_2562946 877348793012156463792155 := by
  unfold tailWord_2562946
  simp only [CollatzResearch.WordTrace]
  refine ⟨23369580043222958293383173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62318880115261222115688461 23369580043222958293383173)
  ·
    refine ⟨4381796258104304680009345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23369580043222958293383173 4381796258104304680009345)
    ·
      refine ⟨3286347193578228510007009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4381796258104304680009345 3286347193578228510007009)
      ·
        refine ⟨2464760395183671382505257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3286347193578228510007009 2464760395183671382505257)
        ·
          refine ⟨1848570296387753536878943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464760395183671382505257 1848570296387753536878943)
          ·
            refine ⟨2772855444581630305318415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848570296387753536878943 2772855444581630305318415)
            ·
              refine ⟨4159283166872445457977623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772855444581630305318415 4159283166872445457977623)
              ·
                refine ⟨6238924750308668186966435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159283166872445457977623 6238924750308668186966435)
                ·
                  refine ⟨9358387125463002280449653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6238924750308668186966435 9358387125463002280449653)
                  ·
                    refine ⟨877348793012156463792155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9358387125463002280449653 877348793012156463792155)
                    ·
                      rfl

theorem cell22_2562946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2562946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2562946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2562946 prefixEnd_2562946 := by exact prefixLift 2562946
  have htrace : WordTrace (prefixWord ++ tailWord_2562946) baseStart_2562946 baseEnd_2562946 := by
    simpa [prefixWord, tailWord_2562946, baseEnd_2562946] using wordTrace_append hprefix tailTrace_2562946
  have hstable : (prefixWord ++ tailWord_2562946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2562946).length < 2 ^ (prefixWord ++ tailWord_2562946).sum := by decide
  have hdescent : baseEnd_2562946 < baseStart_2562946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2562946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563047 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 2, 3]
def baseStart_2563047 : Nat := 118140960795 + 2563047 * 2 ^ 59
def prefixEnd_2563047 : Nat := 4983230072969 + 3 ^ 40 * 2563047 * 2
def baseEnd_2563047 : Nat := 877383367376225867016845

theorem tailTrace_2563047 : CollatzResearch.WordTrace tailWord_2563047 prefixEnd_2563047 877383367376225867016845 := by
  unfold tailWord_2563047
  simp only [CollatzResearch.WordTrace]
  refine ⟨93482003945525927422959395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62321335963683951615306263 93482003945525927422959395)
  ·
    refine ⟨140223005918288891134439093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93482003945525927422959395 140223005918288891134439093)
    ·
      refine ⟨13145906804839583543853665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140223005918288891134439093 13145906804839583543853665)
      ·
        refine ⟨9859430103629687657890249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13145906804839583543853665 9859430103629687657890249)
        ·
          refine ⟨7394572577722265743417687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9859430103629687657890249 7394572577722265743417687)
          ·
            refine ⟨11091858866583398615126531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7394572577722265743417687 11091858866583398615126531)
            ·
              refine ⟨16637788299875097922689797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11091858866583398615126531 16637788299875097922689797)
              ·
                refine ⟨3119585306226580860504337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16637788299875097922689797 3119585306226580860504337)
                ·
                  refine ⟨2339688979669935645378253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3119585306226580860504337 2339688979669935645378253)
                  ·
                    refine ⟨877383367376225867016845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2339688979669935645378253 877383367376225867016845)
                    ·
                      rfl

theorem cell22_2563047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_2563047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563047 prefixEnd_2563047 := by exact prefixLift 2563047
  have htrace : WordTrace (prefixWord ++ tailWord_2563047) baseStart_2563047 baseEnd_2563047 := by
    simpa [prefixWord, tailWord_2563047, baseEnd_2563047] using wordTrace_append hprefix tailTrace_2563047
  have hstable : (prefixWord ++ tailWord_2563047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563047).length < 2 ^ (prefixWord ++ tailWord_2563047).sum := by decide
  have hdescent : baseEnd_2563047 < baseStart_2563047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563105 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 7]
def baseStart_2563105 : Nat := 118140960795 + 2563105 * 2 ^ 59
def prefixEnd_2563105 : Nat := 4983230072969 + 3 ^ 40 * 2563105 * 2
def baseEnd_2563105 : Nat := 292467740653844349688889

theorem tailTrace_2563105 : CollatzResearch.WordTrace tailWord_2563105 prefixEnd_2563105 292467740653844349688889 := by
  unfold tailWord_2563105
  simp only [CollatzResearch.WordTrace]
  refine ⟨93484119379315803328570769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62322746252877202219047179 93484119379315803328570769)
  ·
    refine ⟨70113089534486852496428077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93484119379315803328570769 70113089534486852496428077)
    ·
      refine ⟨26292408575432569686160529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70113089534486852496428077 26292408575432569686160529)
      ·
        refine ⟨19719306431574427264620397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26292408575432569686160529 19719306431574427264620397)
        ·
          refine ⟨7394739911840410224232649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19719306431574427264620397 7394739911840410224232649)
          ·
            refine ⟨5546054933880307668174487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7394739911840410224232649 5546054933880307668174487)
            ·
              refine ⟨8319082400820461502261731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5546054933880307668174487 8319082400820461502261731)
              ·
                refine ⟨12478623601230692253392597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8319082400820461502261731 12478623601230692253392597)
                ·
                  refine ⟨292467740653844349688889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12478623601230692253392597 292467740653844349688889)
                  ·
                    rfl

theorem cell22_2563105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_2563105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563105 prefixEnd_2563105 := by exact prefixLift 2563105
  have htrace : WordTrace (prefixWord ++ tailWord_2563105) baseStart_2563105 baseEnd_2563105 := by
    simpa [prefixWord, tailWord_2563105, baseEnd_2563105] using wordTrace_append hprefix tailTrace_2563105
  have hstable : (prefixWord ++ tailWord_2563105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563105).length < 2 ^ (prefixWord ++ tailWord_2563105).sum := by decide
  have hdescent : baseEnd_2563105 < baseStart_2563105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563122 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_2563122 : Nat := 118140960795 + 2563122 * 2 ^ 59
def prefixEnd_2563122 : Nat := 4983230072969 + 3 ^ 40 * 2563122 * 2
def baseEnd_2563122 : Nat := 292469680469650223797205

theorem tailTrace_2563122 : CollatzResearch.WordTrace tailWord_2563122 prefixEnd_2563122 292469680469650223797205 := by
  unfold tailWord_2563122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23371184855063553807984905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62323159613502810154626413 23371184855063553807984905)
  ·
    refine ⟨17528388641297665355988679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23371184855063553807984905 17528388641297665355988679)
    ·
      refine ⟨26292582961946498033983019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17528388641297665355988679 26292582961946498033983019)
      ·
        refine ⟨39438874442919747050974529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26292582961946498033983019 39438874442919747050974529)
        ·
          refine ⟨29579155832189810288230897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39438874442919747050974529 29579155832189810288230897)
          ·
            refine ⟨22184366874142357716173173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29579155832189810288230897 22184366874142357716173173)
            ·
              refine ⟨2079784394450846035891235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22184366874142357716173173 2079784394450846035891235)
              ·
                refine ⟨3119676591676269053836853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079784394450846035891235 3119676591676269053836853)
                ·
                  refine ⟨292469680469650223797205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3119676591676269053836853 292469680469650223797205)
                  ·
                    rfl

theorem cell22_2563122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_2563122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563122 prefixEnd_2563122 := by exact prefixLift 2563122
  have htrace : WordTrace (prefixWord ++ tailWord_2563122) baseStart_2563122 baseEnd_2563122 := by
    simpa [prefixWord, tailWord_2563122, baseEnd_2563122] using wordTrace_append hprefix tailTrace_2563122
  have hstable : (prefixWord ++ tailWord_2563122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563122).length < 2 ^ (prefixWord ++ tailWord_2563122).sum := by decide
  have hdescent : baseEnd_2563122 < baseStart_2563122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563180 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_2563180 : Nat := 118140960795 + 2563180 * 2 ^ 59
def prefixEnd_2563180 : Nat := 4983230072969 + 3 ^ 40 * 2563180 * 2
def baseEnd_2563180 : Nat := 877428895994257853441437

theorem tailTrace_2563180 : CollatzResearch.WordTrace tailWord_2563180 prefixEnd_2563180 877428895994257853441437 := by
  unfold tailWord_2563180
  simp only [CollatzResearch.WordTrace]
  refine ⟨46743427427022045568775497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62324569902696060758367329 46743427427022045568775497)
  ·
    refine ⟨35057570570266534176581623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46743427427022045568775497 35057570570266534176581623)
    ·
      refine ⟨52586355855399801264872435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35057570570266534176581623 52586355855399801264872435)
      ·
        refine ⟨78879533783099701897308653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52586355855399801264872435 78879533783099701897308653)
        ·
          refine ⟨29579825168662388211490745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78879533783099701897308653 29579825168662388211490745)
          ·
            refine ⟨22184868876496791158618059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29579825168662388211490745 22184868876496791158618059)
            ·
              refine ⟨33277303314745186737927089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22184868876496791158618059 33277303314745186737927089)
              ·
                refine ⟨24957977486058890053445317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33277303314745186737927089 24957977486058890053445317)
                ·
                  refine ⟨4679620778636041885020997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24957977486058890053445317 4679620778636041885020997)
                  ·
                    refine ⟨877428895994257853441437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4679620778636041885020997 877428895994257853441437)
                    ·
                      rfl

theorem cell22_2563180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_2563180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563180 prefixEnd_2563180 := by exact prefixLift 2563180
  have htrace : WordTrace (prefixWord ++ tailWord_2563180) baseStart_2563180 baseEnd_2563180 := by
    simpa [prefixWord, tailWord_2563180, baseEnd_2563180] using wordTrace_append hprefix tailTrace_2563180
  have hstable : (prefixWord ++ tailWord_2563180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563180).length < 2 ^ (prefixWord ++ tailWord_2563180).sum := by decide
  have hdescent : baseEnd_2563180 < baseStart_2563180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563197 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_2563197 : Nat := 118140960795 + 2563197 * 2 ^ 59
def prefixEnd_2563197 : Nat := 4983230072969 + 3 ^ 40 * 2563197 * 2
def baseEnd_2563197 : Nat := 877434715441675475766385

theorem tailTrace_2563197 : CollatzResearch.WordTrace tailWord_2563197 prefixEnd_2563197 877434715441675475766385 := by
  unfold tailWord_2563197
  simp only [CollatzResearch.WordTrace]
  refine ⟨93487474894982503040919845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62324983263321668693946563 93487474894982503040919845)
  ·
    refine ⟨17528901542809219320172471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93487474894982503040919845 17528901542809219320172471)
    ·
      refine ⟨26293352314213828980258707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17528901542809219320172471 26293352314213828980258707)
      ·
        refine ⟨39440028471320743470388061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26293352314213828980258707 39440028471320743470388061)
        ·
          refine ⟨14790010676745278801395523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39440028471320743470388061 14790010676745278801395523)
          ·
            refine ⟨22185016015117918202093285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14790010676745278801395523 22185016015117918202093285)
            ·
              refine ⟨4159690502834609662892491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22185016015117918202093285 4159690502834609662892491)
              ·
                refine ⟨6239535754251914494338737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159690502834609662892491 6239535754251914494338737)
                ·
                  refine ⟨4679651815688935870754053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6239535754251914494338737 4679651815688935870754053)
                  ·
                    refine ⟨877434715441675475766385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4679651815688935870754053 877434715441675475766385)
                    ·
                      rfl

theorem cell22_2563197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_2563197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563197 prefixEnd_2563197 := by exact prefixLift 2563197
  have htrace : WordTrace (prefixWord ++ tailWord_2563197) baseStart_2563197 baseEnd_2563197 := by
    simpa [prefixWord, tailWord_2563197, baseEnd_2563197] using wordTrace_append hprefix tailTrace_2563197
  have hstable : (prefixWord ++ tailWord_2563197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563197).length < 2 ^ (prefixWord ++ tailWord_2563197).sum := by decide
  have hdescent : baseEnd_2563197 < baseStart_2563197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563255 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2563255 : Nat := 118140960795 + 2563255 * 2 ^ 59
def prefixEnd_2563255 : Nat := 4983230072969 + 3 ^ 40 * 2563255 * 2
def baseEnd_2563255 : Nat := 877454570026982657816207

theorem tailTrace_2563255 : CollatzResearch.WordTrace tailWord_2563255 prefixEnd_2563255 877454570026982657816207 := by
  unfold tailWord_2563255
  simp only [CollatzResearch.WordTrace]
  refine ⟨93489590328772378946531219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62326393552514919297687479 93489590328772378946531219)
  ·
    refine ⟨140234385493158568419796829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93489590328772378946531219 140234385493158568419796829)
    ·
      refine ⟨52587894559934463157423811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140234385493158568419796829 52587894559934463157423811)
      ·
        refine ⟨78881841839901694736135717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52587894559934463157423811 78881841839901694736135717)
        ·
          refine ⟨14790345344981567763025447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78881841839901694736135717 14790345344981567763025447)
          ·
            refine ⟨22185518017472351644538171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14790345344981567763025447 22185518017472351644538171)
            ·
              refine ⟨33278277026208527466807257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22185518017472351644538171 33278277026208527466807257)
              ·
                refine ⟨24958707769656395600105443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33278277026208527466807257 24958707769656395600105443)
                ·
                  refine ⟨37438061654484593400158165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24958707769656395600105443 37438061654484593400158165)
                  ·
                    refine ⟨877454570026982657816207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37438061654484593400158165 877454570026982657816207)
                    ·
                      rfl

theorem cell22_2563255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2563255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563255 prefixEnd_2563255 := by exact prefixLift 2563255
  have htrace : WordTrace (prefixWord ++ tailWord_2563255) baseStart_2563255 baseEnd_2563255 := by
    simpa [prefixWord, tailWord_2563255, baseEnd_2563255] using wordTrace_append hprefix tailTrace_2563255
  have hstable : (prefixWord ++ tailWord_2563255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563255).length < 2 ^ (prefixWord ++ tailWord_2563255).sum := by decide
  have hdescent : baseEnd_2563255 < baseStart_2563255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563274 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_2563274 : Nat := 118140960795 + 2563274 * 2 ^ 59
def prefixEnd_2563274 : Nat := 4983230072969 + 3 ^ 40 * 2563274 * 2
def baseEnd_2563274 : Nat := 292487024705090980530383

theorem tailTrace_2563274 : CollatzResearch.WordTrace tailWord_2563274 prefixEnd_2563274 292487024705090980530383 := by
  unfold tailWord_2563274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23372570828925886297868219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62326855543802363460981917 23372570828925886297868219)
  ·
    refine ⟨35058856243388829446802329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23372570828925886297868219 35058856243388829446802329)
    ·
      refine ⟨26294142182541622085101747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35058856243388829446802329 26294142182541622085101747)
      ·
        refine ⟨39441213273812433127652621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26294142182541622085101747 39441213273812433127652621)
        ·
          refine ⟨14790454977679662422869733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39441213273812433127652621 14790454977679662422869733)
          ·
            refine ⟨2773210308314936704288075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14790454977679662422869733 2773210308314936704288075)
            ·
              refine ⟨4159815462472405056432113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773210308314936704288075 4159815462472405056432113)
              ·
                refine ⟨3119861596854303792324085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159815462472405056432113 3119861596854303792324085)
                ·
                  refine ⟨292487024705090980530383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3119861596854303792324085 292487024705090980530383)
                  ·
                    rfl

theorem cell22_2563274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_2563274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563274 prefixEnd_2563274 := by exact prefixLift 2563274
  have htrace : WordTrace (prefixWord ++ tailWord_2563274) baseStart_2563274 baseEnd_2563274 := by
    simpa [prefixWord, tailWord_2563274, baseEnd_2563274] using wordTrace_append hprefix tailTrace_2563274
  have hstable : (prefixWord ++ tailWord_2563274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563274).length < 2 ^ (prefixWord ++ tailWord_2563274).sum := by decide
  have hdescent : baseEnd_2563274 < baseStart_2563274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563304 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_2563304 : Nat := 118140960795 + 2563304 * 2 ^ 59
def prefixEnd_2563304 : Nat := 4983230072969 + 3 ^ 40 * 2563304 * 2
def baseEnd_2563304 : Nat := 877471343728362863341057

theorem tailTrace_2563304 : CollatzResearch.WordTrace tailWord_2563304 prefixEnd_2563304 877471343728362863341057 := by
  unfold tailWord_2563304
  simp only [CollatzResearch.WordTrace]
  refine ⟨46745688752797430157532483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62327585003729906876709977 46745688752797430157532483)
  ·
    refine ⟨70118533129196145236298725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46745688752797430157532483 70118533129196145236298725)
    ·
      refine ⟨13147224961724277231806011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70118533129196145236298725 13147224961724277231806011)
      ·
        refine ⟨19720837442586415847709017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13147224961724277231806011 19720837442586415847709017)
        ·
          refine ⟨14790628081939811885781763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19720837442586415847709017 14790628081939811885781763)
          ·
            refine ⟨22185942122909717828672645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14790628081939811885781763 22185942122909717828672645)
            ·
              refine ⟨4159864148045572092876121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22185942122909717828672645 4159864148045572092876121)
              ·
                refine ⟨3119898111034179069657091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159864148045572092876121 3119898111034179069657091)
                ·
                  refine ⟨4679847166551268604485637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119898111034179069657091 4679847166551268604485637)
                  ·
                    refine ⟨877471343728362863341057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4679847166551268604485637 877471343728362863341057)
                    ·
                      rfl

theorem cell22_2563304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_2563304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563304 prefixEnd_2563304 := by exact prefixLift 2563304
  have htrace : WordTrace (prefixWord ++ tailWord_2563304) baseStart_2563304 baseEnd_2563304 := by
    simpa [prefixWord, tailWord_2563304, baseEnd_2563304] using wordTrace_append hprefix tailTrace_2563304
  have hstable : (prefixWord ++ tailWord_2563304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563304).length < 2 ^ (prefixWord ++ tailWord_2563304).sum := by decide
  have hdescent : baseEnd_2563304 < baseStart_2563304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563336 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 6]
def baseStart_2563336 : Nat := 118140960795 + 2563336 * 2 ^ 59
def prefixEnd_2563336 : Nat := 4983230072969 + 3 ^ 40 * 2563336 * 2
def baseEnd_2563336 : Nat := 292494099327441815513653

theorem tailTrace_2563336 : CollatzResearch.WordTrace tailWord_2563336 prefixEnd_2563336 292494099327441815513653 := by
  unfold tailWord_2563336
  simp only [CollatzResearch.WordTrace]
  refine ⟨46746272320739464890114931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62328363094319286520153241 46746272320739464890114931)
  ·
    refine ⟨70119408481109197335172397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46746272320739464890114931 70119408481109197335172397)
    ·
      refine ⟨26294778180415949000689649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70119408481109197335172397 26294778180415949000689649)
      ·
        refine ⟨19721083635311961750517237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26294778180415949000689649 19721083635311961750517237)
        ·
          refine ⟨1848851590810496414110991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19721083635311961750517237 1848851590810496414110991)
          ·
            refine ⟨2773277386215744621166487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848851590810496414110991 2773277386215744621166487)
            ·
              refine ⟨4159916079323616931749731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773277386215744621166487 4159916079323616931749731)
              ·
                refine ⟨6239874118985425397624597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159916079323616931749731 6239874118985425397624597)
                ·
                  refine ⟨292494099327441815513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6239874118985425397624597 292494099327441815513653)
                  ·
                    rfl

theorem cell22_2563336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_2563336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563336 prefixEnd_2563336 := by exact prefixLift 2563336
  have htrace : WordTrace (prefixWord ++ tailWord_2563336) baseStart_2563336 baseEnd_2563336 := by
    simpa [prefixWord, tailWord_2563336, baseEnd_2563336] using wordTrace_append hprefix tailTrace_2563336
  have hstable : (prefixWord ++ tailWord_2563336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563336).length < 2 ^ (prefixWord ++ tailWord_2563336).sum := by decide
  have hdescent : baseEnd_2563336 < baseStart_2563336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563439 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 1, 4]
def baseStart_2563439 : Nat := 118140960795 + 2563439 * 2 ^ 59
def prefixEnd_2563439 : Nat := 4983230072969 + 3 ^ 40 * 2563439 * 2
def baseEnd_2563439 : Nat := 877517556987267511215643

theorem tailTrace_2563439 : CollatzResearch.WordTrace tailWord_2563439 prefixEnd_2563439 877517556987267511215643 := by
  unfold tailWord_2563439
  simp only [CollatzResearch.WordTrace]
  refine ⟨93496301360105778371229371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62330867573403852247486247 93496301360105778371229371)
  ·
    refine ⟨140244452040158667556844057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93496301360105778371229371 140244452040158667556844057)
    ·
      refine ⟨105183339030119000667633043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140244452040158667556844057 105183339030119000667633043)
      ·
        refine ⟨157775008545178501001449565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105183339030119000667633043 157775008545178501001449565)
        ·
          refine ⟨59165628204441937875543587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157775008545178501001449565 59165628204441937875543587)
          ·
            refine ⟨88748442306662906813315381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59165628204441937875543587 88748442306662906813315381)
            ·
              refine ⟨8320166466249647513748317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88748442306662906813315381 8320166466249647513748317)
              ·
                refine ⟨3120062424843617817655619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8320166466249647513748317 3120062424843617817655619)
                ·
                  refine ⟨4680093637265426726483429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120062424843617817655619 4680093637265426726483429)
                  ·
                    refine ⟨877517556987267511215643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680093637265426726483429 877517556987267511215643)
                    ·
                      rfl

theorem cell22_2563439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_2563439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563439 prefixEnd_2563439 := by exact prefixLift 2563439
  have htrace : WordTrace (prefixWord ++ tailWord_2563439) baseStart_2563439 baseEnd_2563439 := by
    simpa [prefixWord, tailWord_2563439, baseEnd_2563439] using wordTrace_append hprefix tailTrace_2563439
  have hstable : (prefixWord ++ tailWord_2563439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563439).length < 2 ^ (prefixWord ++ tailWord_2563439).sum := by decide
  have hdescent : baseEnd_2563439 < baseStart_2563439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563467 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 3, 6]
def baseStart_2563467 : Nat := 118140960795 + 2563467 * 2 ^ 59
def prefixEnd_2563467 : Nat := 4983230072969 + 3 ^ 40 * 2563467 * 2
def baseEnd_2563467 : Nat := 877527141959484771515557

theorem tailTrace_2563467 : CollatzResearch.WordTrace tailWord_2563467 prefixEnd_2563467 877527141959484771515557 := by
  unfold tailWord_2563467
  simp only [CollatzResearch.WordTrace]
  refine ⟨93497322604004339153248655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62331548402669559435499103 93497322604004339153248655)
  ·
    refine ⟨140245983906006508729872983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93497322604004339153248655 140245983906006508729872983)
    ·
      refine ⟨210368975859009763094809475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140245983906006508729872983 210368975859009763094809475)
      ·
        refine ⟨315553463788514644642214213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210368975859009763094809475 315553463788514644642214213)
        ·
          refine ⟨59166274460346495870415165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315553463788514644642214213 59166274460346495870415165)
          ·
            refine ⟨22187352922629935951405687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59166274460346495870415165 22187352922629935951405687)
            ·
              refine ⟨33281029383944903927108531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22187352922629935951405687 33281029383944903927108531)
              ·
                refine ⟨49921544075917355890662797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33281029383944903927108531 49921544075917355890662797)
                ·
                  refine ⟨18720579028469008458998549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49921544075917355890662797 18720579028469008458998549)
                  ·
                    refine ⟨877527141959484771515557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18720579028469008458998549 877527141959484771515557)
                    ·
                      rfl

theorem cell22_2563467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_2563467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563467 prefixEnd_2563467 := by exact prefixLift 2563467
  have htrace : WordTrace (prefixWord ++ tailWord_2563467) baseStart_2563467 baseEnd_2563467 := by
    simpa [prefixWord, tailWord_2563467, baseEnd_2563467] using wordTrace_append hprefix tailTrace_2563467
  have hstable : (prefixWord ++ tailWord_2563467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563467).length < 2 ^ (prefixWord ++ tailWord_2563467).sum := by decide
  have hdescent : baseEnd_2563467 < baseStart_2563467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563501 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2563501 : Nat := 118140960795 + 2563501 * 2 ^ 59
def prefixEnd_2563501 : Nat := 4983230072969 + 3 ^ 40 * 2563501 * 2
def baseEnd_2563501 : Nat := 877538780854320016165453

theorem tailTrace_2563501 : CollatzResearch.WordTrace tailWord_2563501 prefixEnd_2563501 877538780854320016165453 := by
  unfold tailWord_2563501
  simp only [CollatzResearch.WordTrace]
  refine ⟨93498562685881162959986357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62332375123920775306657571 93498562685881162959986357)
  ·
    refine ⟨8765490251801359027498721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93498562685881162959986357 8765490251801359027498721)
    ·
      refine ⟨6574117688851019270624041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8765490251801359027498721 6574117688851019270624041)
      ·
        refine ⟨4930588266638264452968031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6574117688851019270624041 4930588266638264452968031)
        ·
          refine ⟨7395882399957396679452047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4930588266638264452968031 7395882399957396679452047)
          ·
            refine ⟨11093823599936095019178071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7395882399957396679452047 11093823599936095019178071)
            ·
              refine ⟨16640735399904142528767107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11093823599936095019178071 16640735399904142528767107)
              ·
                refine ⟨24961103099856213793150661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16640735399904142528767107 24961103099856213793150661)
                ·
                  refine ⟨4680206831223040086215749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24961103099856213793150661 4680206831223040086215749)
                  ·
                    refine ⟨877538780854320016165453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680206831223040086215749 877538780854320016165453)
                    ·
                      rfl

theorem cell22_2563501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2563501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563501 prefixEnd_2563501 := by exact prefixLift 2563501
  have htrace : WordTrace (prefixWord ++ tailWord_2563501) baseStart_2563501 baseEnd_2563501 := by
    simpa [prefixWord, tailWord_2563501, baseEnd_2563501] using wordTrace_append hprefix tailTrace_2563501
  have hstable : (prefixWord ++ tailWord_2563501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563501).length < 2 ^ (prefixWord ++ tailWord_2563501).sum := by decide
  have hdescent : baseEnd_2563501 < baseStart_2563501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563516 : List Nat := [2, 2, 2, 4, 2, 1, 2, 7]
def baseStart_2563516 : Nat := 118140960795 + 2563516 * 2 ^ 59
def prefixEnd_2563516 : Nat := 4983230072969 + 3 ^ 40 * 2563516 * 2
def baseEnd_2563516 : Nat := 97504879517873886337823

theorem tailTrace_2563516 : CollatzResearch.WordTrace tailWord_2563516 prefixEnd_2563516 97504879517873886337823 := by
  unfold tailWord_2563516
  simp only [CollatzResearch.WordTrace]
  refine ⟨46749554890413410260891201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62332739853884547014521601 46749554890413410260891201)
  ·
    refine ⟨35062166167810057695668401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46749554890413410260891201 35062166167810057695668401)
    ·
      refine ⟨26296624625857543271751301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35062166167810057695668401 26296624625857543271751301)
      ·
        refine ⟨4930617117348289363453369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26296624625857543271751301 4930617117348289363453369)
        ·
          refine ⟨3697962838011217022590027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4930617117348289363453369 3697962838011217022590027)
          ·
            refine ⟨5546944257016825533885041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697962838011217022590027 5546944257016825533885041)
            ·
              refine ⟨4160208192762619150413781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5546944257016825533885041 4160208192762619150413781)
              ·
                refine ⟨97504879517873886337823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4160208192762619150413781 97504879517873886337823)
                ·
                  rfl

theorem cell22_2563516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 7].length) (baseStart_2563516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563516 prefixEnd_2563516 := by exact prefixLift 2563516
  have htrace : WordTrace (prefixWord ++ tailWord_2563516) baseStart_2563516 baseEnd_2563516 := by
    simpa [prefixWord, tailWord_2563516, baseEnd_2563516] using wordTrace_append hprefix tailTrace_2563516
  have hstable : (prefixWord ++ tailWord_2563516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563516).length < 2 ^ (prefixWord ++ tailWord_2563516).sum := by decide
  have hdescent : baseEnd_2563516 < baseStart_2563516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563591 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2563591 : Nat := 118140960795 + 2563591 * 2 ^ 59
def prefixEnd_2563591 : Nat := 4983230072969 + 3 ^ 40 * 2563591 * 2
def baseEnd_2563591 : Nat := 877569589693589781415177

theorem tailTrace_2563591 : CollatzResearch.WordTrace tailWord_2563591 prefixEnd_2563591 877569589693589781415177 := by
  unfold tailWord_2563591
  simp only [CollatzResearch.WordTrace]
  refine ⟨93501845255555108330762627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62334563503703405553841751 93501845255555108330762627)
  ·
    refine ⟨140252767883332662496143941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93501845255555108330762627 140252767883332662496143941)
    ·
      refine ⟨26297393978124874218026989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140252767883332662496143941 26297393978124874218026989)
      ·
        refine ⟨9861522741796827831760121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26297393978124874218026989 9861522741796827831760121)
        ·
          refine ⟨7396142056347620873820091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9861522741796827831760121 7396142056347620873820091)
          ·
            refine ⟨11094213084521431310730137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396142056347620873820091 11094213084521431310730137)
            ·
              refine ⟨8320659813391073483047603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11094213084521431310730137 8320659813391073483047603)
              ·
                refine ⟨12480989720086610224571405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8320659813391073483047603 12480989720086610224571405)
                ·
                  refine ⟨4680371145032478834214277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12480989720086610224571405 4680371145032478834214277)
                  ·
                    refine ⟨877569589693589781415177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680371145032478834214277 877569589693589781415177)
                    ·
                      rfl

theorem cell22_2563591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2563591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563591 prefixEnd_2563591 := by exact prefixLift 2563591
  have htrace : WordTrace (prefixWord ++ tailWord_2563591) baseStart_2563591 baseEnd_2563591 := by
    simpa [prefixWord, tailWord_2563591, baseEnd_2563591] using wordTrace_append hprefix tailTrace_2563591
  have hstable : (prefixWord ++ tailWord_2563591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563591).length < 2 ^ (prefixWord ++ tailWord_2563591).sum := by decide
  have hdescent : baseEnd_2563591 < baseStart_2563591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563608 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_2563608 : Nat := 118140960795 + 2563608 * 2 ^ 59
def prefixEnd_2563608 : Nat := 4983230072969 + 3 ^ 40 * 2563608 * 2
def baseEnd_2563608 : Nat := 877575409141007403740125

theorem tailTrace_2563608 : CollatzResearch.WordTrace tailWord_2563608 prefixEnd_2563608 877575409141007403740125 := by
  unfold tailWord_2563608
  simp only [CollatzResearch.WordTrace]
  refine ⟨46751232648246760117065739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62334976864329013489420985 46751232648246760117065739)
  ·
    refine ⟨70126848972370140175598609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46751232648246760117065739 70126848972370140175598609)
    ·
      refine ⟨52595136729277605131698957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70126848972370140175598609 52595136729277605131698957)
      ·
        refine ⟨19723176273479101924387109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52595136729277605131698957 19723176273479101924387109)
        ·
          refine ⟨3698095551277331610822583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19723176273479101924387109 3698095551277331610822583)
          ·
            refine ⟨5547143326915997416233875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698095551277331610822583 5547143326915997416233875)
            ·
              refine ⟨8320714990373996124350813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547143326915997416233875 8320714990373996124350813)
              ·
                refine ⟨3120268121390248546631555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8320714990373996124350813 3120268121390248546631555)
                ·
                  refine ⟨4680402182085372819947333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120268121390248546631555 4680402182085372819947333)
                  ·
                    refine ⟨877575409141007403740125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4680402182085372819947333 877575409141007403740125)
                    ·
                      rfl

theorem cell22_2563608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_2563608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563608 prefixEnd_2563608 := by exact prefixLift 2563608
  have htrace : WordTrace (prefixWord ++ tailWord_2563608) baseStart_2563608 baseEnd_2563608 := by
    simpa [prefixWord, tailWord_2563608, baseEnd_2563608] using wordTrace_append hprefix tailTrace_2563608
  have hstable : (prefixWord ++ tailWord_2563608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563608).length < 2 ^ (prefixWord ++ tailWord_2563608).sum := by decide
  have hdescent : baseEnd_2563608 < baseStart_2563608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563634 : List Nat := [3, 2, 1, 1, 2, 1, 1, 11]
def baseStart_2563634 : Nat := 118140960795 + 2563634 * 2 ^ 59
def prefixEnd_2563634 : Nat := 4983230072969 + 3 ^ 40 * 2563634 * 2
def baseEnd_2563634 : Nat := 97509367719150222510005

theorem tailTrace_2563634 : CollatzResearch.WordTrace tailWord_2563634 prefixEnd_2563634 97509367719150222510005 := by
  unfold tailWord_2563634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375853398599831668644489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62335609062932884449718637 23375853398599831668644489)
  ·
    refine ⟨17531890048949873751483367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23375853398599831668644489 17531890048949873751483367)
    ·
      refine ⟨26297835073424810627225051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17531890048949873751483367 26297835073424810627225051)
      ·
        refine ⟨39446752610137215940837577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26297835073424810627225051 39446752610137215940837577)
        ·
          refine ⟨29585064457602911955628183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39446752610137215940837577 29585064457602911955628183)
          ·
            refine ⟨44377596686404367933442275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29585064457602911955628183 44377596686404367933442275)
            ·
              refine ⟨66566395029606551900163413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44377596686404367933442275 66566395029606551900163413)
              ·
                refine ⟨97509367719150222510005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66566395029606551900163413 97509367719150222510005)
                ·
                  rfl

theorem cell22_2563634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_2563634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563634 prefixEnd_2563634 := by exact prefixLift 2563634
  have htrace : WordTrace (prefixWord ++ tailWord_2563634) baseStart_2563634 baseEnd_2563634 := by
    simpa [prefixWord, tailWord_2563634, baseEnd_2563634] using wordTrace_append hprefix tailTrace_2563634
  have hstable : (prefixWord ++ tailWord_2563634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563634).length < 2 ^ (prefixWord ++ tailWord_2563634).sum := by decide
  have hdescent : baseEnd_2563634 < baseStart_2563634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563683 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 3, 3]
def baseStart_2563683 : Nat := 118140960795 + 2563683 * 2 ^ 59
def prefixEnd_2563683 : Nat := 4983230072969 + 3 ^ 40 * 2563683 * 2
def baseEnd_2563683 : Nat := 877601083173732208114895

theorem tailTrace_2563683 : CollatzResearch.WordTrace tailWord_2563683 prefixEnd_2563683 877601083173732208114895 := by
  unfold tailWord_2563683
  simp only [CollatzResearch.WordTrace]
  refine ⟨93505200771221808043111703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62336800514147872028741135 93505200771221808043111703)
  ·
    refine ⟨140257801156832712064667555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93505200771221808043111703 140257801156832712064667555)
    ·
      refine ⟨210386701735249068097001333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140257801156832712064667555 210386701735249068097001333)
      ·
        refine ⟨19723753287679600134093875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210386701735249068097001333 19723753287679600134093875)
        ·
          refine ⟨29585629931519400201140813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19723753287679600134093875 29585629931519400201140813)
          ·
            refine ⟨11094611224319775075427805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29585629931519400201140813 11094611224319775075427805)
            ·
              refine ⟨4160479209119915653285427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11094611224319775075427805 4160479209119915653285427)
              ·
                refine ⟨6240718813679873479928141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160479209119915653285427 6240718813679873479928141)
                ·
                  refine ⟨2340269555129952554973053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6240718813679873479928141 2340269555129952554973053)
                  ·
                    refine ⟨877601083173732208114895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340269555129952554973053 877601083173732208114895)
                    ·
                      rfl

theorem cell22_2563683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 3].length) (baseStart_2563683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563683 prefixEnd_2563683 := by exact prefixLift 2563683
  have htrace : WordTrace (prefixWord ++ tailWord_2563683) baseStart_2563683 baseEnd_2563683 := by
    simpa [prefixWord, tailWord_2563683, baseEnd_2563683] using wordTrace_append hprefix tailTrace_2563683
  have hstable : (prefixWord ++ tailWord_2563683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563683).length < 2 ^ (prefixWord ++ tailWord_2563683).sum := by decide
  have hdescent : baseEnd_2563683 < baseStart_2563683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563730 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_2563730 : Nat := 118140960795 + 2563730 * 2 ^ 59
def prefixEnd_2563730 : Nat := 4983230072969 + 3 ^ 40 * 2563730 * 2
def baseEnd_2563730 : Nat := 292539057411413250729917

theorem tailTrace_2563730 : CollatzResearch.WordTrace tailWord_2563730 prefixEnd_2563730 292539057411413250729917 := by
  unfold tailWord_2563730
  simp only [CollatzResearch.WordTrace]
  refine ⟨23376728750512883767518161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62337943334701023380048429 23376728750512883767518161)
  ·
    refine ⟨17532546562884662825638621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23376728750512883767518161 17532546562884662825638621)
    ·
      refine ⟨6574704961081748559614483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17532546562884662825638621 6574704961081748559614483)
      ·
        refine ⟨9862057441622622839421725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574704961081748559614483 9862057441622622839421725)
        ·
          refine ⟨3698271540608483564783147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9862057441622622839421725 3698271540608483564783147)
          ·
            refine ⟨5547407310912725347174721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698271540608483564783147 5547407310912725347174721)
            ·
              refine ⟨4160555483184544010381041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5547407310912725347174721 4160555483184544010381041)
              ·
                refine ⟨3120416612388408007785781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4160555483184544010381041 3120416612388408007785781)
                ·
                  refine ⟨292539057411413250729917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3120416612388408007785781 292539057411413250729917)
                  ·
                    rfl

theorem cell22_2563730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_2563730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563730 prefixEnd_2563730 := by exact prefixLift 2563730
  have htrace : WordTrace (prefixWord ++ tailWord_2563730) baseStart_2563730 baseEnd_2563730 := by
    simpa [prefixWord, tailWord_2563730, baseEnd_2563730] using wordTrace_append hprefix tailTrace_2563730
  have hstable : (prefixWord ++ tailWord_2563730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563730).length < 2 ^ (prefixWord ++ tailWord_2563730).sum := by decide
  have hdescent : baseEnd_2563730 < baseStart_2563730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563741 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 6]
def baseStart_2563741 : Nat := 118140960795 + 2563741 * 2 ^ 59
def prefixEnd_2563741 : Nat := 4983230072969 + 3 ^ 40 * 2563741 * 2
def baseEnd_2563741 : Nat := 292540312586346463388239

theorem tailTrace_2563741 : CollatzResearch.WordTrace tailWord_2563741 prefixEnd_2563741 292540312586346463388239 := by
  unfold tailWord_2563741
  simp only [CollatzResearch.WordTrace]
  refine ⟨93507316205011683948723077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62338210803341122632482051 93507316205011683948723077)
  ·
    refine ⟨17532621788439690740385577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93507316205011683948723077 17532621788439690740385577)
    ·
      refine ⟨13149466341329768055289183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17532621788439690740385577 13149466341329768055289183)
      ·
        refine ⟨19724199511994652082933775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13149466341329768055289183 19724199511994652082933775)
        ·
          refine ⟨29586299267991978124400663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19724199511994652082933775 29586299267991978124400663)
          ·
            refine ⟨44379448901987967186600995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29586299267991978124400663 44379448901987967186600995)
            ·
              refine ⟨66569173352981950779901493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44379448901987967186600995 66569173352981950779901493)
              ·
                refine ⟨6240860001842057885615765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66569173352981950779901493 6240860001842057885615765)
                ·
                  refine ⟨292540312586346463388239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6240860001842057885615765 292540312586346463388239)
                  ·
                    rfl

theorem cell22_2563741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_2563741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563741 prefixEnd_2563741 := by exact prefixLift 2563741
  have htrace : WordTrace (prefixWord ++ tailWord_2563741) baseStart_2563741 baseEnd_2563741 := by
    simpa [prefixWord, tailWord_2563741, baseEnd_2563741] using wordTrace_append hprefix tailTrace_2563741
  have hstable : (prefixWord ++ tailWord_2563741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563741).length < 2 ^ (prefixWord ++ tailWord_2563741).sum := by decide
  have hdescent : baseEnd_2563741 < baseStart_2563741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563773 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_2563773 : Nat := 118140960795 + 2563773 * 2 ^ 59
def prefixEnd_2563773 : Nat := 4983230072969 + 3 ^ 40 * 2563773 * 2
def baseEnd_2563773 : Nat := 877631892013001973364619

theorem tailTrace_2563773 : CollatzResearch.WordTrace tailWord_2563773 prefixEnd_2563773 877631892013001973364619 := by
  unfold tailWord_2563773
  simp only [CollatzResearch.WordTrace]
  refine ⟨93508483340895753413887973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62338988893930502275925315 93508483340895753413887973)
  ·
    refine ⟨17532840626417953765103995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93508483340895753413887973 17532840626417953765103995)
    ·
      refine ⟨26299260939626930647655993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17532840626417953765103995 26299260939626930647655993)
      ·
        refine ⟨19724445704720197985741995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26299260939626930647655993 19724445704720197985741995)
        ·
          refine ⟨29586668557080296978612993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19724445704720197985741995 29586668557080296978612993)
          ·
            refine ⟨22190001417810222733959745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29586668557080296978612993 22190001417810222733959745)
            ·
              refine ⟨16642501063357667050469809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22190001417810222733959745 16642501063357667050469809)
              ·
                refine ⟨12481875797518250287852357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16642501063357667050469809 12481875797518250287852357)
                ·
                  refine ⟨2340351712034671928972317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12481875797518250287852357 2340351712034671928972317)
                  ·
                    refine ⟨877631892013001973364619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340351712034671928972317 877631892013001973364619)
                    ·
                      rfl

theorem cell22_2563773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_2563773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563773 prefixEnd_2563773 := by exact prefixLift 2563773
  have htrace : WordTrace (prefixWord ++ tailWord_2563773) baseStart_2563773 baseEnd_2563773 := by
    simpa [prefixWord, tailWord_2563773, baseEnd_2563773] using wordTrace_append hprefix tailTrace_2563773
  have hstable : (prefixWord ++ tailWord_2563773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563773).length < 2 ^ (prefixWord ++ tailWord_2563773).sum := by decide
  have hdescent : baseEnd_2563773 < baseStart_2563773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563831 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 7]
def baseStart_2563831 : Nat := 118140960795 + 2563831 * 2 ^ 59
def prefixEnd_2563831 : Nat := 4983230072969 + 3 ^ 40 * 2563831 * 2
def baseEnd_2563831 : Nat := 292550582199436385138147

theorem tailTrace_2563831 : CollatzResearch.WordTrace tailWord_2563831 prefixEnd_2563831 292550582199436385138147 := by
  unfold tailWord_2563831
  simp only [CollatzResearch.WordTrace]
  refine ⟨93510598774685629319499347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62340399183123752879666231 93510598774685629319499347)
  ·
    refine ⟨140265898162028443979249021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93510598774685629319499347 140265898162028443979249021)
    ·
      refine ⟨52599711810760666492218383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140265898162028443979249021 52599711810760666492218383)
      ·
        refine ⟨78899567716140999738327575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52599711810760666492218383 78899567716140999738327575)
        ·
          refine ⟨118349351574211499607491363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78899567716140999738327575 118349351574211499607491363)
          ·
            refine ⟨177524027361317249411237045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118349351574211499607491363 177524027361317249411237045)
            ·
              refine ⟨16642877565123492132303473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177524027361317249411237045 16642877565123492132303473)
              ·
                refine ⟨12482158173842619099227605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16642877565123492132303473 12482158173842619099227605)
                ·
                  refine ⟨292550582199436385138147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12482158173842619099227605 292550582199436385138147)
                  ·
                    rfl

theorem cell22_2563831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 7].length) (baseStart_2563831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563831 prefixEnd_2563831 := by exact prefixLift 2563831
  have htrace : WordTrace (prefixWord ++ tailWord_2563831) baseStart_2563831 baseEnd_2563831 := by
    simpa [prefixWord, tailWord_2563831, baseEnd_2563831] using wordTrace_append hprefix tailTrace_2563831
  have hstable : (prefixWord ++ tailWord_2563831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563831).length < 2 ^ (prefixWord ++ tailWord_2563831).sum := by decide
  have hdescent : baseEnd_2563831 < baseStart_2563831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563835 : List Nat := [1, 1, 1, 1, 1, 3, 1, 9, 1, 3]
def baseStart_2563835 : Nat := 118140960795 + 2563835 * 2 ^ 59
def prefixEnd_2563835 : Nat := 4983230072969 + 3 ^ 40 * 2563835 * 2
def baseEnd_2563835 : Nat := 877653115880054478314429

theorem tailTrace_2563835 : CollatzResearch.WordTrace tailWord_2563835 prefixEnd_2563835 877653115880054478314429 := by
  unfold tailWord_2563835
  simp only [CollatzResearch.WordTrace]
  refine ⟨93510744666671138002644959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62340496444447425335096639 93510744666671138002644959)
  ·
    refine ⟨140266117000006707003967439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93510744666671138002644959 140266117000006707003967439)
    ·
      refine ⟨210399175500010060505951159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140266117000006707003967439 210399175500010060505951159)
      ·
        refine ⟨315598763250015090758926739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210399175500010060505951159 315598763250015090758926739)
        ·
          refine ⟨473398144875022636138390109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315598763250015090758926739 473398144875022636138390109)
          ·
            refine ⟨177524304328133488551896291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 473398144875022636138390109 177524304328133488551896291)
            ·
              refine ⟨266286456492200232827844437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177524304328133488551896291 266286456492200232827844437)
              ·
                refine ⟨1560272206008985739225651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 266286456492200232827844437 1560272206008985739225651)
                ·
                  refine ⟨2340408309013478608838477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560272206008985739225651 2340408309013478608838477)
                  ·
                    refine ⟨877653115880054478314429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340408309013478608838477 877653115880054478314429)
                    ·
                      rfl

theorem cell22_2563835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 3].length) (baseStart_2563835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563835 prefixEnd_2563835 := by exact prefixLift 2563835
  have htrace : WordTrace (prefixWord ++ tailWord_2563835) baseStart_2563835 baseEnd_2563835 := by
    simpa [prefixWord, tailWord_2563835, baseEnd_2563835] using wordTrace_append hprefix tailTrace_2563835
  have hstable : (prefixWord ++ tailWord_2563835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563835).length < 2 ^ (prefixWord ++ tailWord_2563835).sum := by decide
  have hdescent : baseEnd_2563835 < baseStart_2563835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563848 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 5]
def baseStart_2563848 : Nat := 118140960795 + 2563848 * 2 ^ 59
def prefixEnd_2563848 : Nat := 4983230072969 + 3 ^ 40 * 2563848 * 2
def baseEnd_2563848 : Nat := 292552522015242259246463

theorem tailTrace_2563848 : CollatzResearch.WordTrace tailWord_2563848 prefixEnd_2563848 292552522015242259246463 := by
  unfold tailWord_2563848
  simp only [CollatzResearch.WordTrace]
  refine ⟨46755609407812020611434099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62340812543749360815245465 46755609407812020611434099)
  ·
    refine ⟨70133414111718030917151149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46755609407812020611434099 70133414111718030917151149)
    ·
      refine ⟨26300030291894261593931681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70133414111718030917151149 26300030291894261593931681)
      ·
        refine ⟨19725022718920696195448761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26300030291894261593931681 19725022718920696195448761)
        ·
          refine ⟨14793767039190522146586571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19725022718920696195448761 14793767039190522146586571)
          ·
            refine ⟨22190650558785783219879857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14793767039190522146586571 22190650558785783219879857)
            ·
              refine ⟨16642987919089337414909893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22190650558785783219879857 16642987919089337414909893)
              ·
                refine ⟨3120560234829250765295605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16642987919089337414909893 3120560234829250765295605)
                ·
                  refine ⟨292552522015242259246463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3120560234829250765295605 292552522015242259246463)
                  ·
                    rfl

theorem cell22_2563848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_2563848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563848 prefixEnd_2563848 := by exact prefixLift 2563848
  have htrace : WordTrace (prefixWord ++ tailWord_2563848) baseStart_2563848 baseEnd_2563848 := by
    simpa [prefixWord, tailWord_2563848, baseEnd_2563848] using wordTrace_append hprefix tailTrace_2563848
  have hstable : (prefixWord ++ tailWord_2563848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563848).length < 2 ^ (prefixWord ++ tailWord_2563848).sum := by decide
  have hdescent : baseEnd_2563848 < baseStart_2563848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563925 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2563925 : Nat := 118140960795 + 2563925 * 2 ^ 59
def prefixEnd_2563925 : Nat := 4983230072969 + 3 ^ 40 * 2563925 * 2
def baseEnd_2563925 : Nat := 877683924719324243564153

theorem tailTrace_2563925 : CollatzResearch.WordTrace tailWord_2563925 prefixEnd_2563925 877683924719324243564153 := by
  unfold tailWord_2563925
  simp only [CollatzResearch.WordTrace]
  refine ⟨93514027236345083373421229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62342684824230055582280819 93514027236345083373421229)
  ·
    refine ⟨35067760213629406265032961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93514027236345083373421229 35067760213629406265032961)
    ·
      refine ⟨26300820160222054698774721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35067760213629406265032961 26300820160222054698774721)
      ·
        refine ⟨19725615120166541024081041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26300820160222054698774721 19725615120166541024081041)
        ·
          refine ⟨14794211340124905768060781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19725615120166541024081041 14794211340124905768060781)
          ·
            refine ⟨5547829252546839663022793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14794211340124905768060781 5547829252546839663022793)
            ·
              refine ⟨4160871939410129747267095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5547829252546839663022793 4160871939410129747267095)
              ·
                refine ⟨6241307909115194620900643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160871939410129747267095 6241307909115194620900643)
                ·
                  refine ⟨9361961863672791931350965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241307909115194620900643 9361961863672791931350965)
                  ·
                    refine ⟨877683924719324243564153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9361961863672791931350965 877683924719324243564153)
                    ·
                      rfl

theorem cell22_2563925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2563925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563925 prefixEnd_2563925 := by exact prefixLift 2563925
  have htrace : WordTrace (prefixWord ++ tailWord_2563925) baseStart_2563925 baseEnd_2563925 := by
    simpa [prefixWord, tailWord_2563925, baseEnd_2563925] using wordTrace_append hprefix tailTrace_2563925
  have hstable : (prefixWord ++ tailWord_2563925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563925).length < 2 ^ (prefixWord ++ tailWord_2563925).sum := by decide
  have hdescent : baseEnd_2563925 < baseStart_2563925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563940 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_2563940 : Nat := 118140960795 + 2563940 * 2 ^ 59
def prefixEnd_2563940 : Nat := 4983230072969 + 3 ^ 40 * 2563940 * 2
def baseEnd_2563940 : Nat := 877689059525869204439107

theorem tailTrace_2563940 : CollatzResearch.WordTrace tailWord_2563940 prefixEnd_2563940 877689059525869204439107 := by
  unfold tailWord_2563940
  simp only [CollatzResearch.WordTrace]
  refine ⟨46757287165645370467608637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62343049554193827290144849 46757287165645370467608637)
  ·
    refine ⟨17533982687117013925353239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46757287165645370467608637 17533982687117013925353239)
    ·
      refine ⟨26300974030675520888029859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17533982687117013925353239 26300974030675520888029859)
      ·
        refine ⟨39451461046013281332044789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26300974030675520888029859 39451461046013281332044789)
        ·
          refine ⟨3698574473063745124879199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39451461046013281332044789 3698574473063745124879199)
          ·
            refine ⟨5547861709595617687318799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698574473063745124879199 5547861709595617687318799)
            ·
              refine ⟨8321792564393426530978199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547861709595617687318799 8321792564393426530978199)
              ·
                refine ⟨12482688846590139796467299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8321792564393426530978199 12482688846590139796467299)
                ·
                  refine ⟨18724033269885209694700949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12482688846590139796467299 18724033269885209694700949)
                  ·
                    refine ⟨877689059525869204439107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18724033269885209694700949 877689059525869204439107)
                    ·
                      rfl

theorem cell22_2563940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_2563940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563940 prefixEnd_2563940 := by exact prefixLift 2563940
  have htrace : WordTrace (prefixWord ++ tailWord_2563940) baseStart_2563940 baseEnd_2563940 := by
    simpa [prefixWord, tailWord_2563940, baseEnd_2563940] using wordTrace_append hprefix tailTrace_2563940
  have hstable : (prefixWord ++ tailWord_2563940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563940).length < 2 ^ (prefixWord ++ tailWord_2563940).sum := by decide
  have hdescent : baseEnd_2563940 < baseStart_2563940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2563946 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2563946 : Nat := 118140960795 + 2563946 * 2 ^ 59
def prefixEnd_2563946 : Nat := 4983230072969 + 3 ^ 40 * 2563946 * 2
def baseEnd_2563946 : Nat := 877691113448487188789089

theorem tailTrace_2563946 : CollatzResearch.WordTrace tailWord_2563946 prefixEnd_2563946 877691113448487188789089 := by
  unfold tailWord_2563946
  simp only [CollatzResearch.WordTrace]
  refine ⟨23378698292317250989983923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62343195446179335973290461 23378698292317250989983923)
  ·
    refine ⟨35068047438475876484975885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23378698292317250989983923 35068047438475876484975885)
    ·
      refine ⟨13150517789428453681865957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35068047438475876484975885 13150517789428453681865957)
      ·
        refine ⟨2465722085517835065349867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13150517789428453681865957 2465722085517835065349867)
        ·
          refine ⟨3698583128276752598024801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465722085517835065349867 3698583128276752598024801)
          ·
            refine ⟨2773937346207564448518601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3698583128276752598024801 2773937346207564448518601)
            ·
              refine ⟨2080453009655673336388951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2773937346207564448518601 2080453009655673336388951)
              ·
                refine ⟨3120679514483510004583427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080453009655673336388951 3120679514483510004583427)
                ·
                  refine ⟨4681019271725265006875141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120679514483510004583427 4681019271725265006875141)
                  ·
                    refine ⟨877691113448487188789089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4681019271725265006875141 877691113448487188789089)
                    ·
                      rfl

theorem cell22_2563946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2563946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2563946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2563946 prefixEnd_2563946 := by exact prefixLift 2563946
  have htrace : WordTrace (prefixWord ++ tailWord_2563946) baseStart_2563946 baseEnd_2563946 := by
    simpa [prefixWord, tailWord_2563946, baseEnd_2563946] using wordTrace_append hprefix tailTrace_2563946
  have hstable : (prefixWord ++ tailWord_2563946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2563946).length < 2 ^ (prefixWord ++ tailWord_2563946).sum := by decide
  have hdescent : baseEnd_2563946 < baseStart_2563946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2563946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564004 : List Nat := [2, 3, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_2564004 : Nat := 118140960795 + 2564004 * 2 ^ 59
def prefixEnd_2564004 : Nat := 4983230072969 + 3 ^ 40 * 2564004 * 2
def baseEnd_2564004 : Nat := 877710968033794370838911

theorem tailTrace_2564004 : CollatzResearch.WordTrace tailWord_2564004 prefixEnd_2564004 877710968033794370838911 := by
  unfold tailWord_2564004
  simp only [CollatzResearch.WordTrace]
  refine ⟨46758454301529439932773533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62344605735372586577031377 46758454301529439932773533)
  ·
    refine ⟨17534420363073539974790075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46758454301529439932773533 17534420363073539974790075)
    ·
      refine ⟨26301630544610309962185113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17534420363073539974790075 26301630544610309962185113)
      ·
        refine ⟨19726222908457732471638835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26301630544610309962185113 19726222908457732471638835)
        ·
          refine ⟨29589334362686598707458253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19726222908457732471638835 29589334362686598707458253)
          ·
            refine ⟨11096000386007474515296845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29589334362686598707458253 11096000386007474515296845)
            ·
              refine ⟨4161000144752802943236317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11096000386007474515296845 4161000144752802943236317)
              ·
                refine ⟨1560375054282301103713619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4161000144752802943236317 1560375054282301103713619)
                ·
                  refine ⟨2340562581423451655570429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560375054282301103713619 2340562581423451655570429)
                  ·
                    refine ⟨877710968033794370838911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340562581423451655570429 877710968033794370838911)
                    ·
                      rfl

theorem cell22_2564004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_2564004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564004 prefixEnd_2564004 := by exact prefixLift 2564004
  have htrace : WordTrace (prefixWord ++ tailWord_2564004) baseStart_2564004 baseEnd_2564004 := by
    simpa [prefixWord, tailWord_2564004, baseEnd_2564004] using wordTrace_append hprefix tailTrace_2564004
  have hstable : (prefixWord ++ tailWord_2564004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564004).length < 2 ^ (prefixWord ++ tailWord_2564004).sum := by decide
  have hdescent : baseEnd_2564004 < baseStart_2564004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564021 : List Nat := [1, 3, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2564021 : Nat := 118140960795 + 2564021 * 2 ^ 59
def prefixEnd_2564021 : Nat := 4983230072969 + 3 ^ 40 * 2564021 * 2
def baseEnd_2564021 : Nat := 877716787481211993163859

theorem tailTrace_2564021 : CollatzResearch.WordTrace tailWord_2564021 prefixEnd_2564021 877716787481211993163859 := by
  unfold tailWord_2564021
  simp only [CollatzResearch.WordTrace]
  refine ⟨93517528643997291768915917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62345019095998194512610611 93517528643997291768915917)
  ·
    refine ⟨35069073241498984413343469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93517528643997291768915917 35069073241498984413343469)
    ·
      refine ⟨13150902465562119155003801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35069073241498984413343469 13150902465562119155003801)
      ·
        refine ⟨9863176849171589366252851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13150902465562119155003801 9863176849171589366252851)
        ·
          refine ⟨14794765273757384049379277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863176849171589366252851 14794765273757384049379277)
          ·
            refine ⟨5548036977659019018517229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14794765273757384049379277 5548036977659019018517229)
            ·
              refine ⟨2080513866622132131943961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5548036977659019018517229 2080513866622132131943961)
              ·
                refine ⟨1560385399966599098957971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080513866622132131943961 1560385399966599098957971)
                ·
                  refine ⟨2340578099949898648436957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560385399966599098957971 2340578099949898648436957)
                  ·
                    refine ⟨877716787481211993163859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340578099949898648436957 877716787481211993163859)
                    ·
                      rfl

theorem cell22_2564021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2564021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564021 prefixEnd_2564021 := by exact prefixLift 2564021
  have htrace : WordTrace (prefixWord ++ tailWord_2564021) baseStart_2564021 baseEnd_2564021 := by
    simpa [prefixWord, tailWord_2564021, baseEnd_2564021] using wordTrace_append hprefix tailTrace_2564021
  have hstable : (prefixWord ++ tailWord_2564021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564021).length < 2 ^ (prefixWord ++ tailWord_2564021).sum := by decide
  have hdescent : baseEnd_2564021 < baseStart_2564021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564094 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2564094 : Nat := 118140960795 + 2564094 * 2 ^ 59
def prefixEnd_2564094 : Nat := 4983230072969 + 3 ^ 40 * 2564094 * 2
def baseEnd_2564094 : Nat := 877741776873064136088635

theorem tailTrace_2564094 : CollatzResearch.WordTrace tailWord_2564094 prefixEnd_2564094 877741776873064136088635 := by
  unfold tailWord_2564094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11690023896591603154540417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62346794115155216824215557 11690023896591603154540417)
  ·
    refine ⟨8767517922443702365905313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11690023896591603154540417 8767517922443702365905313)
    ·
      refine ⟨6575638441832776774428985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8767517922443702365905313 6575638441832776774428985)
      ·
        refine ⟨4931728831374582580821739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6575638441832776774428985 4931728831374582580821739)
        ·
          refine ⟨7397593247061873871232609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4931728831374582580821739 7397593247061873871232609)
          ·
            refine ⟨5548194935296405403424457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7397593247061873871232609 5548194935296405403424457)
            ·
              refine ⟨4161146201472304052568343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5548194935296405403424457 4161146201472304052568343)
              ·
                refine ⟨6241719302208456078852515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161146201472304052568343 6241719302208456078852515)
                ·
                  refine ⟨9362578953312684118278773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241719302208456078852515 9362578953312684118278773)
                  ·
                    refine ⟨877741776873064136088635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9362578953312684118278773 877741776873064136088635)
                    ·
                      rfl

theorem cell22_2564094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2564094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564094 prefixEnd_2564094 := by exact prefixLift 2564094
  have htrace : WordTrace (prefixWord ++ tailWord_2564094) baseStart_2564094 baseEnd_2564094 := by
    simpa [prefixWord, tailWord_2564094, baseEnd_2564094] using wordTrace_append hprefix tailTrace_2564094
  have hstable : (prefixWord ++ tailWord_2564094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564094).length < 2 ^ (prefixWord ++ tailWord_2564094).sum := by decide
  have hdescent : baseEnd_2564094 < baseStart_2564094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564190 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2564190 : Nat := 118140960795 + 2564190 * 2 ^ 59
def prefixEnd_2564190 : Nat := 4983230072969 + 3 ^ 40 * 2564190 * 2
def baseEnd_2564190 : Nat := 877774639634951885688341

theorem tailTrace_2564190 : CollatzResearch.WordTrace tailWord_2564190 prefixEnd_2564190 877774639634951885688341 := by
  unfold tailWord_2564190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11690461572548129203977253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62349128386923355754545349 11690461572548129203977253)
  ·
    refine ⟨2191961544852774225745735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11690461572548129203977253 2191961544852774225745735)
    ·
      refine ⟨3287942317279161338618603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2191961544852774225745735 3287942317279161338618603)
      ·
        refine ⟨4931913475918742007927905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3287942317279161338618603 4931913475918742007927905)
        ·
          refine ⟨3698935106939056505945929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4931913475918742007927905 3698935106939056505945929)
          ·
            refine ⟨2774201330204292379459447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3698935106939056505945929 2774201330204292379459447)
            ·
              refine ⟨4161301995306438569189171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774201330204292379459447 4161301995306438569189171)
              ·
                refine ⟨6241952992959657853783757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161301995306438569189171 6241952992959657853783757)
                ·
                  refine ⟨2340732372359871695168909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6241952992959657853783757 2340732372359871695168909)
                  ·
                    refine ⟨877774639634951885688341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340732372359871695168909 877774639634951885688341)
                    ·
                      rfl

theorem cell22_2564190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2564190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564190 prefixEnd_2564190 := by exact prefixLift 2564190
  have htrace : WordTrace (prefixWord ++ tailWord_2564190) baseStart_2564190 baseEnd_2564190 := by
    simpa [prefixWord, tailWord_2564190, baseEnd_2564190] using wordTrace_append hprefix tailTrace_2564190
  have hstable : (prefixWord ++ tailWord_2564190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564190).length < 2 ^ (prefixWord ++ tailWord_2564190).sum := by decide
  have hdescent : baseEnd_2564190 < baseStart_2564190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564197 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 6]
def baseStart_2564197 : Nat := 118140960795 + 2564197 * 2 ^ 59
def prefixEnd_2564197 : Nat := 4983230072969 + 3 ^ 40 * 2564197 * 2
def baseEnd_2564197 : Nat := 292592345292668733587773

theorem tailTrace_2564197 : CollatzResearch.WordTrace tailWord_2564197 prefixEnd_2564197 292592345292668733587773 := by
  unfold tailWord_2564197
  simp only [CollatzResearch.WordTrace]
  refine ⟨93523947891359673827322845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62349298594239782551548563 93523947891359673827322845)
  ·
    refine ⟨35071480459259877685246067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93523947891359673827322845 35071480459259877685246067)
    ·
      refine ⟨52607220688889816527869101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35071480459259877685246067 52607220688889816527869101)
      ·
        refine ⟨19727707758333681197950913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52607220688889816527869101 19727707758333681197950913)
        ·
          refine ⟨14795780818750260898463185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19727707758333681197950913 14795780818750260898463185)
          ·
            refine ⟨11096835614062695673847389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14795780818750260898463185 11096835614062695673847389)
            ·
              refine ⟨4161313355273510877692771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11096835614062695673847389 4161313355273510877692771)
              ·
                refine ⟨6241970032910266316539157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161313355273510877692771 6241970032910266316539157)
                ·
                  refine ⟨292592345292668733587773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6241970032910266316539157 292592345292668733587773)
                  ·
                    rfl

theorem cell22_2564197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_2564197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564197 prefixEnd_2564197 := by exact prefixLift 2564197
  have htrace : WordTrace (prefixWord ++ tailWord_2564197) baseStart_2564197 baseEnd_2564197 := by
    simpa [prefixWord, tailWord_2564197, baseEnd_2564197] using wordTrace_append hprefix tailTrace_2564197
  have hstable : (prefixWord ++ tailWord_2564197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564197).length < 2 ^ (prefixWord ++ tailWord_2564197).sum := by decide
  have hdescent : baseEnd_2564197 < baseStart_2564197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564227 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 2, 4]
def baseStart_2564227 : Nat := 118140960795 + 2564227 * 2 ^ 59
def prefixEnd_2564227 : Nat := 4983230072969 + 3 ^ 40 * 2564227 * 2
def baseEnd_2564227 : Nat := 877787305491096122513227

theorem tailTrace_2564227 : CollatzResearch.WordTrace tailWord_2564227 prefixEnd_2564227 877787305491096122513227 := by
  unfold tailWord_2564227
  simp only [CollatzResearch.WordTrace]
  refine ⟨93525042081250988950914935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62350028054167325967276623 93525042081250988950914935)
  ·
    refine ⟨140287563121876483426372403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93525042081250988950914935 140287563121876483426372403)
    ·
      refine ⟨210431344682814725139558605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140287563121876483426372403 210431344682814725139558605)
      ·
        refine ⟨78911754256055521927334477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210431344682814725139558605 78911754256055521927334477)
        ·
          refine ⟨29591907846020820722750429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78911754256055521927334477 29591907846020820722750429)
          ·
            refine ⟨11096965442257807771031411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29591907846020820722750429 11096965442257807771031411)
            ·
              refine ⟨16645448163386711656547117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11096965442257807771031411 16645448163386711656547117)
              ·
                refine ⟨6242043061270016871205169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16645448163386711656547117 6242043061270016871205169)
                ·
                  refine ⟨4681532295952512653403877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6242043061270016871205169 4681532295952512653403877)
                  ·
                    refine ⟨877787305491096122513227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4681532295952512653403877 877787305491096122513227)
                    ·
                      rfl

theorem cell22_2564227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_2564227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564227 prefixEnd_2564227 := by exact prefixLift 2564227
  have htrace : WordTrace (prefixWord ++ tailWord_2564227) baseStart_2564227 baseEnd_2564227 := by
    simpa [prefixWord, tailWord_2564227, baseEnd_2564227] using wordTrace_append hprefix tailTrace_2564227
  have hstable : (prefixWord ++ tailWord_2564227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564227).length < 2 ^ (prefixWord ++ tailWord_2564227).sum := by decide
  have hdescent : baseEnd_2564227 < baseStart_2564227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564248 : List Nat := [2, 1, 2, 4, 3, 2, 2, 2, 4]
def baseStart_2564248 : Nat := 118140960795 + 2564248 * 2 ^ 59
def prefixEnd_2564248 : Nat := 4983230072969 + 3 ^ 40 * 2564248 * 2
def baseEnd_2564248 : Nat := 292598164740086355912721

theorem tailTrace_2564248 : CollatzResearch.WordTrace tailWord_2564248 prefixEnd_2564248 292598164740086355912721 := by
  unfold tailWord_2564248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46762904007087454768714699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62350538676116606358286265 46762904007087454768714699)
  ·
    refine ⟨70144356010631182153072049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46762904007087454768714699 70144356010631182153072049)
    ·
      refine ⟨52608267007973386614804037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70144356010631182153072049 52608267007973386614804037)
      ·
        refine ⟨9864050063995009990275757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52608267007973386614804037 9864050063995009990275757)
        ·
          refine ⟨3699018773998128746353409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9864050063995009990275757 3699018773998128746353409)
          ·
            refine ⟨2774264080498596559765057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3699018773998128746353409 2774264080498596559765057)
            ·
              refine ⟨2080698060373947419823793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774264080498596559765057 2080698060373947419823793)
              ·
                refine ⟨1560523545280460564867845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080698060373947419823793 1560523545280460564867845)
                ·
                  refine ⟨292598164740086355912721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560523545280460564867845 292598164740086355912721)
                  ·
                    rfl

theorem cell22_2564248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_2564248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564248 prefixEnd_2564248 := by exact prefixLift 2564248
  have htrace : WordTrace (prefixWord ++ tailWord_2564248) baseStart_2564248 baseEnd_2564248 := by
    simpa [prefixWord, tailWord_2564248, baseEnd_2564248] using wordTrace_append hprefix tailTrace_2564248
  have hstable : (prefixWord ++ tailWord_2564248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564248).length < 2 ^ (prefixWord ++ tailWord_2564248).sum := by decide
  have hdescent : baseEnd_2564248 < baseStart_2564248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564274 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_2564274 : Nat := 118140960795 + 2564274 * 2 ^ 59
def prefixEnd_2564274 : Nat := 4983230072969 + 3 ^ 40 * 2564274 * 2
def baseEnd_2564274 : Nat := 877803394551603666588083

theorem tailTrace_2564274 : CollatzResearch.WordTrace tailWord_2564274 prefixEnd_2564274 877803394551603666588083 := by
  unfold tailWord_2564274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23381689078020178994468969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62351170874720477318583917 23381689078020178994468969)
  ·
    refine ⟨17536266808515134245851727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23381689078020178994468969 17536266808515134245851727)
    ·
      refine ⟨26304400212772701368777591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17536266808515134245851727 26304400212772701368777591)
      ·
        refine ⟨39456600319159052053166387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26304400212772701368777591 39456600319159052053166387)
        ·
          refine ⟨59184900478738578079749581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39456600319159052053166387 59184900478738578079749581)
          ·
            refine ⟨22194337679526966779906093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59184900478738578079749581 22194337679526966779906093)
            ·
              refine ⟨8322876629822612542464785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22194337679526966779906093 8322876629822612542464785)
              ·
                refine ⟨6242157472366959406848589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8322876629822612542464785 6242157472366959406848589)
                ·
                  refine ⟨2340809052137609777568221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6242157472366959406848589 2340809052137609777568221)
                  ·
                    refine ⟨877803394551603666588083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340809052137609777568221 877803394551603666588083)
                    ·
                      rfl

theorem cell22_2564274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_2564274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564274 prefixEnd_2564274 := by exact prefixLift 2564274
  have htrace : WordTrace (prefixWord ++ tailWord_2564274) baseStart_2564274 baseEnd_2564274 := by
    simpa [prefixWord, tailWord_2564274, baseEnd_2564274] using wordTrace_append hprefix tailTrace_2564274
  have hstable : (prefixWord ++ tailWord_2564274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564274).length < 2 ^ (prefixWord ++ tailWord_2564274).sum := by decide
  have hdescent : baseEnd_2564274 < baseStart_2564274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564332 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 6]
def baseStart_2564332 : Nat := 118140960795 + 2564332 * 2 ^ 59
def prefixEnd_2564332 : Nat := 4983230072969 + 3 ^ 40 * 2564332 * 2
def baseEnd_2564332 : Nat := 292607749712303616212635

theorem tailTrace_2564332 : CollatzResearch.WordTrace tailWord_2564332 prefixEnd_2564332 292607749712303616212635 := by
  unfold tailWord_2564332
  simp only [CollatzResearch.WordTrace]
  refine ⟨46764435872935295941743625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62352581163913727922324833 46764435872935295941743625)
  ·
    refine ⟨35073326904701471956307719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46764435872935295941743625 35073326904701471956307719)
    ·
      refine ⟨52609990357052207934461579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35073326904701471956307719 52609990357052207934461579)
      ·
        refine ⟨78914985535578311901692369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52609990357052207934461579 78914985535578311901692369)
        ·
          refine ⟨59186239151683733926269277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78914985535578311901692369 59186239151683733926269277)
          ·
            refine ⟨22194839681881400222350979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59186239151683733926269277 22194839681881400222350979)
            ·
              refine ⟨33292259522822100333526469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22194839681881400222350979 33292259522822100333526469)
              ·
                refine ⟨6242298660529143812536213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33292259522822100333526469 6242298660529143812536213)
                ·
                  refine ⟨292607749712303616212635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6242298660529143812536213 292607749712303616212635)
                  ·
                    rfl

theorem cell22_2564332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_2564332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564332 prefixEnd_2564332 := by exact prefixLift 2564332
  have htrace : WordTrace (prefixWord ++ tailWord_2564332) baseStart_2564332 baseEnd_2564332 := by
    simpa [prefixWord, tailWord_2564332, baseEnd_2564332] using wordTrace_append hprefix tailTrace_2564332
  have hstable : (prefixWord ++ tailWord_2564332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564332).length < 2 ^ (prefixWord ++ tailWord_2564332).sum := by decide
  have hdescent : baseEnd_2564332 < baseStart_2564332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564364 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_2564364 : Nat := 118140960795 + 2564364 * 2 ^ 59
def prefixEnd_2564364 : Nat := 4983230072969 + 3 ^ 40 * 2564364 * 2
def baseEnd_2564364 : Nat := 877834203390873431837807

theorem tailTrace_2564364 : CollatzResearch.WordTrace tailWord_2564364 prefixEnd_2564364 877834203390873431837807 := by
  unfold tailWord_2564364
  simp only [CollatzResearch.WordTrace]
  refine ⟨46765019440877330674326073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62353359254503107565768097 46765019440877330674326073)
  ·
    refine ⟨35073764580657998005744555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46765019440877330674326073 35073764580657998005744555)
    ·
      refine ⟨52610646870986997008616833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35073764580657998005744555 52610646870986997008616833)
      ·
        refine ⟨39457985153240247756462625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52610646870986997008616833 39457985153240247756462625)
        ·
          refine ⟨29593488864930185817346969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39457985153240247756462625 29593488864930185817346969)
          ·
            refine ⟨22195116648697639363010227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29593488864930185817346969 22195116648697639363010227)
            ·
              refine ⟨33292674973046459044515341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22195116648697639363010227 33292674973046459044515341)
              ·
                refine ⟨12484753114892422141693253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33292674973046459044515341 12484753114892422141693253)
                ·
                  refine ⟨2340891209042329151567485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12484753114892422141693253 2340891209042329151567485)
                  ·
                    refine ⟨877834203390873431837807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340891209042329151567485 877834203390873431837807)
                    ·
                      rfl

theorem cell22_2564364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_2564364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564364 prefixEnd_2564364 := by exact prefixLift 2564364
  have htrace : WordTrace (prefixWord ++ tailWord_2564364) baseStart_2564364 baseEnd_2564364 := by
    simpa [prefixWord, tailWord_2564364, baseEnd_2564364] using wordTrace_append hprefix tailTrace_2564364
  have hstable : (prefixWord ++ tailWord_2564364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564364).length < 2 ^ (prefixWord ++ tailWord_2564364).sum := by decide
  have hdescent : baseEnd_2564364 < baseStart_2564364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564398 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2564398 : Nat := 118140960795 + 2564398 * 2 ^ 59
def prefixEnd_2564398 : Nat := 4983230072969 + 3 ^ 40 * 2564398 * 2
def baseEnd_2564398 : Nat := 877845842285708676487703

theorem tailTrace_2564398 : CollatzResearch.WordTrace tailWord_2564398 prefixEnd_2564398 877845842285708676487703 := by
  unfold tailWord_2564398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691409870453935644423731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62354185975754323436926565 11691409870453935644423731)
  ·
    refine ⟨17537114805680903466635597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11691409870453935644423731 17537114805680903466635597)
    ·
      refine ⟨6576418052130338799988349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17537114805680903466635597 6576418052130338799988349)
      ·
        refine ⟨2466156769548877049995631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6576418052130338799988349 2466156769548877049995631)
        ·
          refine ⟨3699235154323315574993447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466156769548877049995631 3699235154323315574993447)
          ·
            refine ⟨5548852731484973362490171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699235154323315574993447 5548852731484973362490171)
            ·
              refine ⟨8323279097227460043735257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548852731484973362490171 8323279097227460043735257)
              ·
                refine ⟨6242459322920595032801443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8323279097227460043735257 6242459322920595032801443)
                ·
                  refine ⟨9363688984380892549202165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6242459322920595032801443 9363688984380892549202165)
                  ·
                    refine ⟨877845842285708676487703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9363688984380892549202165 877845842285708676487703)
                    ·
                      rfl

theorem cell22_2564398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2564398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564398 prefixEnd_2564398 := by exact prefixLift 2564398
  have htrace : WordTrace (prefixWord ++ tailWord_2564398) baseStart_2564398 baseEnd_2564398 := by
    simpa [prefixWord, tailWord_2564398, baseEnd_2564398] using wordTrace_append hprefix tailTrace_2564398
  have hstable : (prefixWord ++ tailWord_2564398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564398).length < 2 ^ (prefixWord ++ tailWord_2564398).sum := by decide
  have hdescent : baseEnd_2564398 < baseStart_2564398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564407 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2564407 : Nat := 118140960795 + 2564407 * 2 ^ 59
def prefixEnd_2564407 : Nat := 4983230072969 + 3 ^ 40 * 2564407 * 2
def baseEnd_2564407 : Nat := 877848923169635653012675

theorem tailTrace_2564407 : CollatzResearch.WordTrace tailWord_2564407 prefixEnd_2564407 877848923169635653012675 := by
  unfold tailWord_2564407
  simp only [CollatzResearch.WordTrace]
  refine ⟨93531607220598879692467475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62354404813732586461644983 93531607220598879692467475)
  ·
    refine ⟨140297410830898319538701213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93531607220598879692467475 140297410830898319538701213)
    ·
      refine ⟨52611529061586869827012955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140297410830898319538701213 52611529061586869827012955)
      ·
        refine ⟨78917293592380304740519433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52611529061586869827012955 78917293592380304740519433)
        ·
          refine ⟨59187970194285228555389575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78917293592380304740519433 59187970194285228555389575)
          ·
            refine ⟨88781955291427842833084363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59187970194285228555389575 88781955291427842833084363)
            ·
              refine ⟨133172932937141764249626545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88781955291427842833084363 133172932937141764249626545)
              ·
                refine ⟨99879699702856323187219909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133172932937141764249626545 99879699702856323187219909)
                ·
                  refine ⟨18727443694285560597603733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99879699702856323187219909 18727443694285560597603733)
                  ·
                    refine ⟨877848923169635653012675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18727443694285560597603733 877848923169635653012675)
                    ·
                      rfl

theorem cell22_2564407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2564407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564407 prefixEnd_2564407 := by exact prefixLift 2564407
  have htrace : WordTrace (prefixWord ++ tailWord_2564407) baseStart_2564407 baseEnd_2564407 := by
    simpa [prefixWord, tailWord_2564407, baseEnd_2564407] using wordTrace_append hprefix tailTrace_2564407
  have hstable : (prefixWord ++ tailWord_2564407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564407).length < 2 ^ (prefixWord ++ tailWord_2564407).sum := by decide
  have hdescent : baseEnd_2564407 < baseStart_2564407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564417 : List Nat := [1, 2, 5, 2, 3, 1, 2, 2, 4]
def baseStart_2564417 : Nat := 118140960795 + 2564417 * 2 ^ 59
def prefixEnd_2564417 : Nat := 4983230072969 + 3 ^ 40 * 2564417 * 2
def baseEnd_2564417 : Nat := 292617448791332986754215

theorem tailTrace_2564417 : CollatzResearch.WordTrace tailWord_2564417 prefixEnd_2564417 292617448791332986754215 := by
  unfold tailWord_2564417
  simp only [CollatzResearch.WordTrace]
  refine ⟨93531971950562651400331505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62354647967041767600221003 93531971950562651400331505)
  ·
    refine ⟨70148978962921988550248629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93531971950562651400331505 70148978962921988550248629)
    ·
      refine ⟨6576466777773936426585809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70148978962921988550248629 6576466777773936426585809)
      ·
        refine ⟨4932350083330452319939357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6576466777773936426585809 4932350083330452319939357)
        ·
          refine ⟨1849631281248919619977259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4932350083330452319939357 1849631281248919619977259)
          ·
            refine ⟨2774446921873379429965889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849631281248919619977259 2774446921873379429965889)
            ·
              refine ⟨2080835191405034572474417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774446921873379429965889 2080835191405034572474417)
              ·
                refine ⟨1560626393553775929355813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080835191405034572474417 1560626393553775929355813)
                ·
                  refine ⟨292617448791332986754215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560626393553775929355813 292617448791332986754215)
                  ·
                    rfl

theorem cell22_2564417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_2564417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564417 prefixEnd_2564417 := by exact prefixLift 2564417
  have htrace : WordTrace (prefixWord ++ tailWord_2564417) baseStart_2564417 baseEnd_2564417 := by
    simpa [prefixWord, tailWord_2564417, baseEnd_2564417] using wordTrace_append hprefix tailTrace_2564417
  have hstable : (prefixWord ++ tailWord_2564417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564417).length < 2 ^ (prefixWord ++ tailWord_2564417).sum := by decide
  have hdescent : baseEnd_2564417 < baseStart_2564417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564439 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 5]
def baseStart_2564439 : Nat := 118140960795 + 2564439 * 2 ^ 59
def prefixEnd_2564439 : Nat := 4983230072969 + 3 ^ 40 * 2564439 * 2
def baseEnd_2564439 : Nat := 292619959141199412070859

theorem tailTrace_2564439 : CollatzResearch.WordTrace tailWord_2564439 prefixEnd_2564439 292619959141199412070859 := by
  unfold tailWord_2564439
  simp only [CollatzResearch.WordTrace]
  refine ⟨93532774356482949157632371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62355182904321966105088247 93532774356482949157632371)
  ·
    refine ⟨140299161534724423736448557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93532774356482949157632371 140299161534724423736448557)
    ·
      refine ⟨52612185575521658901168209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140299161534724423736448557 52612185575521658901168209)
      ·
        refine ⟨39459139181641244175876157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52612185575521658901168209 39459139181641244175876157)
        ·
          refine ⟨14797177193115466565953559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39459139181641244175876157 14797177193115466565953559)
          ·
            refine ⟨22195765789673199848930339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14797177193115466565953559 22195765789673199848930339)
            ·
              refine ⟨33293648684509799773395509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22195765789673199848930339 33293648684509799773395509)
              ·
                refine ⟨3121279564172793728755829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33293648684509799773395509 3121279564172793728755829)
                ·
                  refine ⟨292619959141199412070859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3121279564172793728755829 292619959141199412070859)
                  ·
                    rfl

theorem cell22_2564439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 5].length) (baseStart_2564439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564439 prefixEnd_2564439 := by exact prefixLift 2564439
  have htrace : WordTrace (prefixWord ++ tailWord_2564439) baseStart_2564439 baseEnd_2564439 := by
    simpa [prefixWord, tailWord_2564439, baseEnd_2564439] using wordTrace_append hprefix tailTrace_2564439
  have hstable : (prefixWord ++ tailWord_2564439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564439).length < 2 ^ (prefixWord ++ tailWord_2564439).sum := by decide
  have hdescent : baseEnd_2564439 < baseStart_2564439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564460 : List Nat := [2, 2, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_2564460 : Nat := 118140960795 + 2564460 * 2 ^ 59
def prefixEnd_2564460 : Nat := 4983230072969 + 3 ^ 40 * 2564460 * 2
def baseEnd_2564460 : Nat := 877867066152761181437513

theorem tailTrace_2564460 : CollatzResearch.WordTrace tailWord_2564460 prefixEnd_2564460 877867066152761181437513 := by
  unfold tailWord_2564460
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766770144703434872073417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62355693526271246496097889 46766770144703434872073417)
  ·
    refine ⟨35075077608527576154055063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46766770144703434872073417 35075077608527576154055063)
    ·
      refine ⟨52612616412791364231082595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35075077608527576154055063 52612616412791364231082595)
      ·
        refine ⟨78918924619187046346623893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52612616412791364231082595 78918924619187046346623893)
        ·
          refine ⟨3699324591524392797497995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78918924619187046346623893 3699324591524392797497995)
          ·
            refine ⟨5548986887286589196246993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699324591524392797497995 5548986887286589196246993)
            ·
              refine ⟨4161740165464941897185245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5548986887286589196246993 4161740165464941897185245)
              ·
                refine ⟨1560652562049353211444467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4161740165464941897185245 1560652562049353211444467)
                ·
                  refine ⟨2340978843074029817166701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560652562049353211444467 2340978843074029817166701)
                  ·
                    refine ⟨877867066152761181437513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340978843074029817166701 877867066152761181437513)
                    ·
                      rfl

theorem cell22_2564460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_2564460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564460 prefixEnd_2564460 := by exact prefixLift 2564460
  have htrace : WordTrace (prefixWord ++ tailWord_2564460) baseStart_2564460 baseEnd_2564460 := by
    simpa [prefixWord, tailWord_2564460, baseEnd_2564460] using wordTrace_append hprefix tailTrace_2564460
  have hstable : (prefixWord ++ tailWord_2564460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564460).length < 2 ^ (prefixWord ++ tailWord_2564460).sum := by decide
  have hdescent : baseEnd_2564460 < baseStart_2564460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564490 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_2564490 : Nat := 118140960795 + 2564490 * 2 ^ 59
def prefixEnd_2564490 : Nat := 4983230072969 + 3 ^ 40 * 2564490 * 2
def baseEnd_2564490 : Nat := 292625778588617034395807

theorem tailTrace_2564490 : CollatzResearch.WordTrace tailWord_2564490 prefixEnd_2564490 292625778588617034395807 := by
  unfold tailWord_2564490
  simp only [CollatzResearch.WordTrace]
  refine ⟨23383658619824546216934731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62356422986198789911825949 23383658619824546216934731)
  ·
    refine ⟨35075487929736819325402097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23383658619824546216934731 35075487929736819325402097)
    ·
      refine ⟨26306615947302614494051573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35075487929736819325402097 26306615947302614494051573)
      ·
        refine ⟨2466245245059620108817335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26306615947302614494051573 2466245245059620108817335)
        ·
          refine ⟨3699367867589430163226003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466245245059620108817335 3699367867589430163226003)
          ·
            refine ⟨5549051801384145244839005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699367867589430163226003 5549051801384145244839005)
            ·
              refine ⟨2080894425519054466814627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5549051801384145244839005 2080894425519054466814627)
              ·
                refine ⟨3121341638278581700221941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080894425519054466814627 3121341638278581700221941)
                ·
                  refine ⟨292625778588617034395807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3121341638278581700221941 292625778588617034395807)
                  ·
                    rfl

theorem cell22_2564490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_2564490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564490 prefixEnd_2564490 := by exact prefixLift 2564490
  have htrace : WordTrace (prefixWord ++ tailWord_2564490) baseStart_2564490 baseEnd_2564490 := by
    simpa [prefixWord, tailWord_2564490, baseEnd_2564490] using wordTrace_append hprefix tailTrace_2564490
  have hstable : (prefixWord ++ tailWord_2564490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564490).length < 2 ^ (prefixWord ++ tailWord_2564490).sum := by decide
  have hdescent : baseEnd_2564490 < baseStart_2564490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564516 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_2564516 : Nat := 118140960795 + 2564516 * 2 ^ 59
def prefixEnd_2564516 : Nat := 4983230072969 + 3 ^ 40 * 2564516 * 2
def baseEnd_2564516 : Nat := 877886236097195702037341

theorem tailTrace_2564516 : CollatzResearch.WordTrace tailWord_2564516 prefixEnd_2564516 877886236097195702037341 := by
  unfold tailWord_2564516
  simp only [CollatzResearch.WordTrace]
  refine ⟨46767791388601995654092701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62357055184802660872123601 46767791388601995654092701)
  ·
    refine ⟨17537921770725748370284763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46767791388601995654092701 17537921770725748370284763)
    ·
      refine ⟨26306882656088622555427145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17537921770725748370284763 26306882656088622555427145)
      ·
        refine ⟨19730161992066466916570359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26306882656088622555427145 19730161992066466916570359)
        ·
          refine ⟨29595242988099700374855539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19730161992066466916570359 29595242988099700374855539)
          ·
            refine ⟨44392864482149550562283309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29595242988099700374855539 44392864482149550562283309)
            ·
              refine ⟨16647324180806081460856241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44392864482149550562283309 16647324180806081460856241)
              ·
                refine ⟨12485493135604561095642181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16647324180806081460856241 12485493135604561095642181)
                ·
                  refine ⟨2341029962925855205432909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12485493135604561095642181 2341029962925855205432909)
                  ·
                    refine ⟨877886236097195702037341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341029962925855205432909 877886236097195702037341)
                    ·
                      rfl

theorem cell22_2564516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_2564516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564516 prefixEnd_2564516 := by exact prefixLift 2564516
  have htrace : WordTrace (prefixWord ++ tailWord_2564516) baseStart_2564516 baseEnd_2564516 := by
    simpa [prefixWord, tailWord_2564516, baseEnd_2564516] using wordTrace_append hprefix tailTrace_2564516
  have hstable : (prefixWord ++ tailWord_2564516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564516).length < 2 ^ (prefixWord ++ tailWord_2564516).sum := by decide
  have hdescent : baseEnd_2564516 < baseStart_2564516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564529 : List Nat := [1, 2, 2, 4, 1, 2, 10]
def baseStart_2564529 : Nat := 118140960795 + 2564529 * 2 ^ 59
def prefixEnd_2564529 : Nat := 4983230072969 + 3 ^ 40 * 2564529 * 2
def baseEnd_2564529 : Nat := 32514469861587703757863

theorem tailTrace_2564529 : CollatzResearch.WordTrace tailWord_2564529 prefixEnd_2564529 32514469861587703757863 := by
  unfold tailWord_2564529
  simp only [CollatzResearch.WordTrace]
  refine ⟨93536056926156894528408641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62357371284104596352272427 93536056926156894528408641)
  ·
    refine ⟨70152042694617670896306481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93536056926156894528408641 70152042694617670896306481)
    ·
      refine ⟨52614032020963253172229861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70152042694617670896306481 52614032020963253172229861)
      ·
        refine ⟨9865131003930609969793099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52614032020963253172229861 9865131003930609969793099)
        ·
          refine ⟨14797696505895914954689649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9865131003930609969793099 14797696505895914954689649)
          ·
            refine ⟨11098272379421936216017237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14797696505895914954689649 11098272379421936216017237)
            ·
              refine ⟨32514469861587703757863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11098272379421936216017237 32514469861587703757863)
              ·
                rfl

theorem cell22_2564529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 10].length) (baseStart_2564529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564529 prefixEnd_2564529 := by exact prefixLift 2564529
  have htrace : WordTrace (prefixWord ++ tailWord_2564529) baseStart_2564529 baseEnd_2564529 := by
    simpa [prefixWord, tailWord_2564529, baseEnd_2564529] using wordTrace_append hprefix tailTrace_2564529
  have hstable : (prefixWord ++ tailWord_2564529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564529).length < 2 ^ (prefixWord ++ tailWord_2564529).sum := by decide
  have hdescent : baseEnd_2564529 < baseStart_2564529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564561 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 3, 3]
def baseStart_2564561 : Nat := 118140960795 + 2564561 * 2 ^ 59
def prefixEnd_2564561 : Nat := 4983230072969 + 3 ^ 40 * 2564561 * 2
def baseEnd_2564561 : Nat := 877901640516830584662203

theorem tailTrace_2564561 : CollatzResearch.WordTrace tailWord_2564561 prefixEnd_2564561 877901640516830584662203 := by
  unfold tailWord_2564561
  simp only [CollatzResearch.WordTrace]
  refine ⟨93537224062040963993573537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62358149374693975995715691 93537224062040963993573537)
  ·
    refine ⟨70152918046530722995180153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93537224062040963993573537 70152918046530722995180153)
    ·
      refine ⟨52614688534898042246385115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70152918046530722995180153 52614688534898042246385115)
      ·
        refine ⟨78922032802347063369577673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52614688534898042246385115 78922032802347063369577673)
        ·
          refine ⟨59191524601760297527183255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78922032802347063369577673 59191524601760297527183255)
          ·
            refine ⟨88787286902640446290774883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59191524601760297527183255 88787286902640446290774883)
            ·
              refine ⟨133180930353960669436162325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88787286902640446290774883 133180930353960669436162325)
              ·
                refine ⟨6242856110341906379820109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 133180930353960669436162325 6242856110341906379820109)
                ·
                  refine ⟨2341071041378214892432541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6242856110341906379820109 2341071041378214892432541)
                  ·
                    refine ⟨877901640516830584662203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341071041378214892432541 877901640516830584662203)
                    ·
                      rfl

theorem cell22_2564561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_2564561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564561 prefixEnd_2564561 := by exact prefixLift 2564561
  have htrace : WordTrace (prefixWord ++ tailWord_2564561) baseStart_2564561 baseEnd_2564561 := by
    simpa [prefixWord, tailWord_2564561, baseEnd_2564561] using wordTrace_append hprefix tailTrace_2564561
  have hstable : (prefixWord ++ tailWord_2564561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564561).length < 2 ^ (prefixWord ++ tailWord_2564561).sum := by decide
  have hdescent : baseEnd_2564561 < baseStart_2564561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564666 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_2564666 : Nat := 118140960795 + 2564666 * 2 ^ 59
def prefixEnd_2564666 : Nat := 4983230072969 + 3 ^ 40 * 2564666 * 2
def baseEnd_2564666 : Nat := 877937584162645310786881

theorem tailTrace_2564666 : CollatzResearch.WordTrace tailWord_2564666 prefixEnd_2564666 877937584162645310786881 := by
  unfold tailWord_2564666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23385263431665141731536463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62360702484440377950763901 23385263431665141731536463)
  ·
    refine ⟨35077895147497712597304695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23385263431665141731536463 35077895147497712597304695)
    ·
      refine ⟨52616842721246568895957043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35077895147497712597304695 52616842721246568895957043)
      ·
        refine ⟨78925264081869853343935565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52616842721246568895957043 78925264081869853343935565)
        ·
          refine ⟨29596974030701195003975837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78925264081869853343935565 29596974030701195003975837)
          ·
            refine ⟨11098865261512948126490939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29596974030701195003975837 11098865261512948126490939)
            ·
              refine ⟨16648297892269422189736409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11098865261512948126490939 16648297892269422189736409)
              ·
                refine ⟨12486223419202066642302307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16648297892269422189736409 12486223419202066642302307)
                ·
                  refine ⟨18729335128803099963453461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12486223419202066642302307 18729335128803099963453461)
                  ·
                    refine ⟨877937584162645310786881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18729335128803099963453461 877937584162645310786881)
                    ·
                      rfl

theorem cell22_2564666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_2564666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564666 prefixEnd_2564666 := by exact prefixLift 2564666
  have htrace : WordTrace (prefixWord ++ tailWord_2564666) baseStart_2564666 baseEnd_2564666 := by
    simpa [prefixWord, tailWord_2564666, baseEnd_2564666] using wordTrace_append hprefix tailTrace_2564666
  have hstable : (prefixWord ++ tailWord_2564666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564666).length < 2 ^ (prefixWord ++ tailWord_2564666).sum := by decide
  have hdescent : baseEnd_2564666 < baseStart_2564666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564668 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_2564668 : Nat := 118140960795 + 2564668 * 2 ^ 59
def prefixEnd_2564668 : Nat := 4983230072969 + 3 ^ 40 * 2564668 * 2
def baseEnd_2564668 : Nat := 877938268803517972236875

theorem tailTrace_2564668 : CollatzResearch.WordTrace tailWord_2564668 prefixEnd_2564668 877938268803517972236875 := by
  unfold tailWord_2564668
  simp only [CollatzResearch.WordTrace]
  refine ⟨46770563336326660633859329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62360751115102214178479105 46770563336326660633859329)
  ·
    refine ⟨35077922502244995475394497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46770563336326660633859329 35077922502244995475394497)
    ·
      refine ⟨26308441876683746606545873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35077922502244995475394497 26308441876683746606545873)
      ·
        refine ⟨19731331407512809954909405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26308441876683746606545873 19731331407512809954909405)
        ·
          refine ⟨7399249277817303733091027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19731331407512809954909405 7399249277817303733091027)
          ·
            refine ⟨11098873916725955599636541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7399249277817303733091027 11098873916725955599636541)
            ·
              refine ⟨4162077718772233349863703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11098873916725955599636541 4162077718772233349863703)
              ·
                refine ⟨6243116578158350024795555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162077718772233349863703 6243116578158350024795555)
                ·
                  refine ⟨9364674867237525037193333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6243116578158350024795555 9364674867237525037193333)
                  ·
                    refine ⟨877938268803517972236875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9364674867237525037193333 877938268803517972236875)
                    ·
                      rfl

theorem cell22_2564668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_2564668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564668 prefixEnd_2564668 := by exact prefixLift 2564668
  have htrace : WordTrace (prefixWord ++ tailWord_2564668) baseStart_2564668 baseEnd_2564668 := by
    simpa [prefixWord, tailWord_2564668, baseEnd_2564668] using wordTrace_append hprefix tailTrace_2564668
  have hstable : (prefixWord ++ tailWord_2564668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564668).length < 2 ^ (prefixWord ++ tailWord_2564668).sum := by decide
  have hdescent : baseEnd_2564668 < baseStart_2564668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564685 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2564685 : Nat := 118140960795 + 2564685 * 2 ^ 59
def prefixEnd_2564685 : Nat := 4983230072969 + 3 ^ 40 * 2564685 * 2
def baseEnd_2564685 : Nat := 877944088250935594561823

theorem tailTrace_2564685 : CollatzResearch.WordTrace tailWord_2564685 prefixEnd_2564685 877944088250935594561823 := by
  unfold tailWord_2564685
  simp only [CollatzResearch.WordTrace]
  refine ⟨93541746713591733171087509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62361164475727822114058339 93541746713591733171087509)
  ·
    refine ⟨4384769377199612492394727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93541746713591733171087509 4384769377199612492394727)
    ·
      refine ⟨6577154065799418738592091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384769377199612492394727 6577154065799418738592091)
      ·
        refine ⟨9865731098699128107888137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577154065799418738592091 9865731098699128107888137)
        ·
          refine ⟨7399298324024346080916103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9865731098699128107888137 7399298324024346080916103)
          ·
            refine ⟨11098947486036519121374155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7399298324024346080916103 11098947486036519121374155)
            ·
              refine ⟨16648421229054778682061233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11098947486036519121374155 16648421229054778682061233)
              ·
                refine ⟨12486315921791084011545925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16648421229054778682061233 12486315921791084011545925)
                ·
                  refine ⟨2341184235335828252164861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12486315921791084011545925 2341184235335828252164861)
                  ·
                    refine ⟨877944088250935594561823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341184235335828252164861 877944088250935594561823)
                    ·
                      rfl

theorem cell22_2564685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2564685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564685 prefixEnd_2564685 := by exact prefixLift 2564685
  have htrace : WordTrace (prefixWord ++ tailWord_2564685) baseStart_2564685 baseEnd_2564685 := by
    simpa [prefixWord, tailWord_2564685, baseEnd_2564685] using wordTrace_append hprefix tailTrace_2564685
  have hstable : (prefixWord ++ tailWord_2564685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564685).length < 2 ^ (prefixWord ++ tailWord_2564685).sum := by decide
  have hdescent : baseEnd_2564685 < baseStart_2564685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564700 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2564700 : Nat := 118140960795 + 2564700 * 2 ^ 59
def prefixEnd_2564700 : Nat := 4983230072969 + 3 ^ 40 * 2564700 * 2
def baseEnd_2564700 : Nat := 877949223057480555436777

theorem tailTrace_2564700 : CollatzResearch.WordTrace tailWord_2564700 prefixEnd_2564700 877949223057480555436777 := by
  unfold tailWord_2564700
  simp only [CollatzResearch.WordTrace]
  refine ⟨46771146904268695366441777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62361529205691593821922369 46771146904268695366441777)
  ·
    refine ⟨35078360178201521524831333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46771146904268695366441777 35078360178201521524831333)
    ·
      refine ⟨6577192533412785285905875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35078360178201521524831333 6577192533412785285905875)
      ·
        refine ⟨9865788800119177928858813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577192533412785285905875 9865788800119177928858813)
        ·
          refine ⟨3699670800044691723322055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9865788800119177928858813 3699670800044691723322055)
          ·
            refine ⟨5549506200067037584983083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699670800044691723322055 5549506200067037584983083)
            ·
              refine ⟨8324259300100556377474625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549506200067037584983083 8324259300100556377474625)
              ·
                refine ⟨6243194475075417283105969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8324259300100556377474625 6243194475075417283105969)
                ·
                  refine ⟨4682395856306562962329477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6243194475075417283105969 4682395856306562962329477)
                  ·
                    refine ⟨877949223057480555436777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4682395856306562962329477 877949223057480555436777)
                    ·
                      rfl

theorem cell22_2564700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2564700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564700 prefixEnd_2564700 := by exact prefixLift 2564700
  have htrace : WordTrace (prefixWord ++ tailWord_2564700) baseStart_2564700 baseEnd_2564700 := by
    simpa [prefixWord, tailWord_2564700, baseEnd_2564700] using wordTrace_append hprefix tailTrace_2564700
  have hstable : (prefixWord ++ tailWord_2564700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564700).length < 2 ^ (prefixWord ++ tailWord_2564700).sum := by decide
  have hdescent : baseEnd_2564700 < baseStart_2564700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564711 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2564711 : Nat := 118140960795 + 2564711 * 2 ^ 59
def prefixEnd_2564711 : Nat := 4983230072969 + 3 ^ 40 * 2564711 * 2
def baseEnd_2564711 : Nat := 877952988582280193411743

theorem tailTrace_2564711 : CollatzResearch.WordTrace tailWord_2564711 prefixEnd_2564711 877952988582280193411743 := by
  unfold tailWord_2564711
  simp only [CollatzResearch.WordTrace]
  refine ⟨93542695011497539611533987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62361796674331693074355991 93542695011497539611533987)
  ·
    refine ⟨140314042517246309417300981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93542695011497539611533987 140314042517246309417300981)
    ·
      refine ⟨13154441485991841507871967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140314042517246309417300981 13154441485991841507871967)
      ·
        refine ⟨19731662228987762261807951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13154441485991841507871967 19731662228987762261807951)
        ·
          refine ⟨29597493343481643392711927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19731662228987762261807951 29597493343481643392711927)
          ·
            refine ⟨44396240015222465089067891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29597493343481643392711927 44396240015222465089067891)
            ·
              refine ⟨66594360022833697633601837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44396240015222465089067891 66594360022833697633601837)
              ·
                refine ⟨24972885008562636612600689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66594360022833697633601837 24972885008562636612600689)
                ·
                  refine ⟨18729663756421977459450517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24972885008562636612600689 18729663756421977459450517)
                  ·
                    refine ⟨877952988582280193411743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18729663756421977459450517 877952988582280193411743)
                    ·
                      rfl

theorem cell22_2564711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2564711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564711 prefixEnd_2564711 := by exact prefixLift 2564711
  have htrace : WordTrace (prefixWord ++ tailWord_2564711) baseStart_2564711 baseEnd_2564711 := by
    simpa [prefixWord, tailWord_2564711, baseEnd_2564711] using wordTrace_append hprefix tailTrace_2564711
  have hstable : (prefixWord ++ tailWord_2564711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564711).length < 2 ^ (prefixWord ++ tailWord_2564711).sum := by decide
  have hdescent : baseEnd_2564711 < baseStart_2564711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564764 : List Nat := [2, 2, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_2564764 : Nat := 118140960795 + 2564764 * 2 ^ 59
def prefixEnd_2564764 : Nat := 4983230072969 + 3 ^ 40 * 2564764 * 2
def baseEnd_2564764 : Nat := 877971131565405721836581

theorem tailTrace_2564764 : CollatzResearch.WordTrace tailWord_2564764 prefixEnd_2564764 877971131565405721836581 := by
  unfold tailWord_2564764
  simp only [CollatzResearch.WordTrace]
  refine ⟨46772314040152764831606673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62363085386870353108808897 46772314040152764831606673)
  ·
    refine ⟨35079235530114573623705005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46772314040152764831606673 35079235530114573623705005)
    ·
      refine ⟨13154713323792965108889377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35079235530114573623705005 13154713323792965108889377)
      ·
        refine ⟨9866034992844723831667033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13154713323792965108889377 9866034992844723831667033)
        ·
          refine ⟨7399526244633542873750275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9866034992844723831667033 7399526244633542873750275)
          ·
            refine ⟨11099289366950314310625413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7399526244633542873750275 11099289366950314310625413)
            ·
              refine ⟨2081116756303183933242265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11099289366950314310625413 2081116756303183933242265)
              ·
                refine ⟨1560837567227387949931699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2081116756303183933242265 1560837567227387949931699)
                ·
                  refine ⟨2341256350841081924897549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560837567227387949931699 2341256350841081924897549)
                  ·
                    refine ⟨877971131565405721836581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341256350841081924897549 877971131565405721836581)
                    ·
                      rfl

theorem cell22_2564764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_2564764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564764 prefixEnd_2564764 := by exact prefixLift 2564764
  have htrace : WordTrace (prefixWord ++ tailWord_2564764) baseStart_2564764 baseEnd_2564764 := by
    simpa [prefixWord, tailWord_2564764, baseEnd_2564764] using wordTrace_append hprefix tailTrace_2564764
  have hstable : (prefixWord ++ tailWord_2564764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564764).length < 2 ^ (prefixWord ++ tailWord_2564764).sum := by decide
  have hdescent : baseEnd_2564764 < baseStart_2564764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564850 : List Nat := [3, 2, 1, 3, 1, 2, 4, 6]
def baseStart_2564850 : Nat := 118140960795 + 2564850 * 2 ^ 59
def prefixEnd_2564850 : Nat := 4983230072969 + 3 ^ 40 * 2564850 * 2
def baseEnd_2564850 : Nat := 97555619013658907131813

theorem tailTrace_2564850 : CollatzResearch.WordTrace tailWord_2564850 prefixEnd_2564850 97555619013658907131813 := by
  unfold tailWord_2564850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23386941189498491587711001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62365176505329310900562669 23386941189498491587711001)
  ·
    refine ⟨17540205892123868690783251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23386941189498491587711001 17540205892123868690783251)
    ·
      refine ⟨26310308838185803036174877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17540205892123868690783251 26310308838185803036174877)
      ·
        refine ⟨9866365814319676138565579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26310308838185803036174877 9866365814319676138565579)
        ·
          refine ⟨14799548721479514207848369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866365814319676138565579 14799548721479514207848369)
          ·
            refine ⟨11099661541109635655886277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14799548721479514207848369 11099661541109635655886277)
            ·
              refine ⟨2081186538958056685478677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11099661541109635655886277 2081186538958056685478677)
              ·
                refine ⟨97555619013658907131813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2081186538958056685478677 97555619013658907131813)
                ·
                  rfl

theorem cell22_2564850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_2564850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564850 prefixEnd_2564850 := by exact prefixLift 2564850
  have htrace : WordTrace (prefixWord ++ tailWord_2564850) baseStart_2564850 baseEnd_2564850 := by
    simpa [prefixWord, tailWord_2564850, baseEnd_2564850] using wordTrace_append hprefix tailTrace_2564850
  have hstable : (prefixWord ++ tailWord_2564850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564850).length < 2 ^ (prefixWord ++ tailWord_2564850).sum := by decide
  have hdescent : baseEnd_2564850 < baseStart_2564850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564895 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 5]
def baseStart_2564895 : Nat := 118140960795 + 2564895 * 2 ^ 59
def prefixEnd_2564895 : Nat := 4983230072969 + 3 ^ 40 * 2564895 * 2
def baseEnd_2564895 : Nat := 292671991847521682270393

theorem tailTrace_2564895 : CollatzResearch.WordTrace tailWord_2564895 prefixEnd_2564895 292671991847521682270393 := by
  unfold tailWord_2564895
  simp only [CollatzResearch.WordTrace]
  refine ⟨93549406042830939036232139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62366270695220626024154759 93549406042830939036232139)
  ·
    refine ⟨140324109064246408554348209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93549406042830939036232139 140324109064246408554348209)
    ·
      refine ⟨105243081798184806415761157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140324109064246408554348209 105243081798184806415761157)
      ·
        refine ⟨19733077837159651202955217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105243081798184806415761157 19733077837159651202955217)
        ·
          refine ⟨14799808377869738402216413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19733077837159651202955217 14799808377869738402216413)
          ·
            refine ⟨5549928141701151900831155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14799808377869738402216413 5549928141701151900831155)
            ·
              refine ⟨8324892212551727851246733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549928141701151900831155 8324892212551727851246733)
              ·
                refine ⟨3121834579706897944217525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8324892212551727851246733 3121834579706897944217525)
                ·
                  refine ⟨292671991847521682270393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3121834579706897944217525 292671991847521682270393)
                  ·
                    rfl

theorem cell22_2564895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 5].length) (baseStart_2564895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564895 prefixEnd_2564895 := by exact prefixLift 2564895
  have htrace : WordTrace (prefixWord ++ tailWord_2564895) baseStart_2564895 baseEnd_2564895 := by
    simpa [prefixWord, tailWord_2564895, baseEnd_2564895] using wordTrace_append hprefix tailTrace_2564895
  have hstable : (prefixWord ++ tailWord_2564895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564895).length < 2 ^ (prefixWord ++ tailWord_2564895).sum := by decide
  have hdescent : baseEnd_2564895 < baseStart_2564895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564929 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 5]
def baseStart_2564929 : Nat := 118140960795 + 2564929 * 2 ^ 59
def prefixEnd_2564929 : Nat := 4983230072969 + 3 ^ 40 * 2564929 * 2
def baseEnd_2564929 : Nat := 292675871479133430487025

theorem tailTrace_2564929 : CollatzResearch.WordTrace tailWord_2564929 prefixEnd_2564929 292675871479133430487025 := by
  unfold tailWord_2564929
  simp only [CollatzResearch.WordTrace]
  refine ⟨93550646124707762842969841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62367097416471841895313227 93550646124707762842969841)
  ·
    refine ⟨70162984593530822132227381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93550646124707762842969841 70162984593530822132227381)
    ·
      refine ⟨6577779805643514574896317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70162984593530822132227381 6577779805643514574896317)
      ·
        refine ⟨2466667427116317965586119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6577779805643514574896317 2466667427116317965586119)
        ·
          refine ⟨3700001140674476948379179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466667427116317965586119 3700001140674476948379179)
          ·
            refine ⟨5550001711011715422568769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700001140674476948379179 5550001711011715422568769)
            ·
              refine ⟨4162501283258786566926577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5550001711011715422568769 4162501283258786566926577)
              ·
                refine ⟨3121875962444089925194933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4162501283258786566926577 3121875962444089925194933)
                ·
                  refine ⟨292675871479133430487025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3121875962444089925194933 292675871479133430487025)
                  ·
                    rfl

theorem cell22_2564929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_2564929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564929 prefixEnd_2564929 := by exact prefixLift 2564929
  have htrace : WordTrace (prefixWord ++ tailWord_2564929) baseStart_2564929 baseEnd_2564929 := by
    simpa [prefixWord, tailWord_2564929, baseEnd_2564929] using wordTrace_append hprefix tailTrace_2564929
  have hstable : (prefixWord ++ tailWord_2564929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564929).length < 2 ^ (prefixWord ++ tailWord_2564929).sum := by decide
  have hdescent : baseEnd_2564929 < baseStart_2564929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2564983 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2564983 : Nat := 118140960795 + 2564983 * 2 ^ 59
def prefixEnd_2564983 : Nat := 4983230072969 + 3 ^ 40 * 2564983 * 2
def baseEnd_2564983 : Nat := 878046099740962150610909

theorem tailTrace_2564983 : CollatzResearch.WordTrace tailWord_2564983 prefixEnd_2564983 878046099740962150610909 := by
  unfold tailWord_2564983
  simp only [CollatzResearch.WordTrace]
  refine ⟨93552615666512130065435603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62368410444341420043623735 93552615666512130065435603)
  ·
    refine ⟨140328923499768195098153405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93552615666512130065435603 140328923499768195098153405)
    ·
      refine ⟨52623346312413073161807527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140328923499768195098153405 52623346312413073161807527)
      ·
        refine ⟨78935019468619609742711291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52623346312413073161807527 78935019468619609742711291)
        ·
          refine ⟨118402529202929414614066937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78935019468619609742711291 118402529202929414614066937)
          ·
            refine ⟨88801896902197060960550203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118402529202929414614066937 88801896902197060960550203)
            ·
              refine ⟨133202845353295591440825305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88801896902197060960550203 133202845353295591440825305)
              ·
                refine ⟨99902134014971693580618979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133202845353295591440825305 99902134014971693580618979)
                ·
                  refine ⟨149853201022457540370928469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99902134014971693580618979 149853201022457540370928469)
                  ·
                    refine ⟨878046099740962150610909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 149853201022457540370928469 878046099740962150610909)
                    ·
                      rfl

theorem cell22_2564983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2564983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2564983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2564983 prefixEnd_2564983 := by exact prefixLift 2564983
  have htrace : WordTrace (prefixWord ++ tailWord_2564983) baseStart_2564983 baseEnd_2564983 := by
    simpa [prefixWord, tailWord_2564983, baseEnd_2564983] using wordTrace_append hprefix tailTrace_2564983
  have hstable : (prefixWord ++ tailWord_2564983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2564983).length < 2 ^ (prefixWord ++ tailWord_2564983).sum := by decide
  have hdescent : baseEnd_2564983 < baseStart_2564983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2564983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565169 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 3, 3]
def baseStart_2565169 : Nat := 118140960795 + 2565169 * 2 ^ 59
def prefixEnd_2565169 : Nat := 4983230072969 + 3 ^ 40 * 2565169 * 2
def baseEnd_2565169 : Nat := 878109771342119665460339

theorem tailTrace_2565169 : CollatzResearch.WordTrace tailWord_2565169 prefixEnd_2565169 878109771342119665460339 := by
  unfold tailWord_2565169
  simp only [CollatzResearch.WordTrace]
  refine ⟨93559399643838283831706561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62372933095892189221137707 93559399643838283831706561)
  ·
    refine ⟨70169549732878712873779921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93559399643838283831706561 70169549732878712873779921)
    ·
      refine ⟨52627162299659034655334941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70169549732878712873779921 52627162299659034655334941)
      ·
        refine ⟨19735185862372137995750603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52627162299659034655334941 19735185862372137995750603)
        ·
          refine ⟨29602778793558206993625905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19735185862372137995750603 29602778793558206993625905)
          ·
            refine ⟨22202084095168655245219429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29602778793558206993625905 22202084095168655245219429)
            ·
              refine ⟨4162890767844122858478643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22202084095168655245219429 4162890767844122858478643)
              ·
                refine ⟨6244336151766184287717965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162890767844122858478643 6244336151766184287717965)
                ·
                  refine ⟨2341626056912319107894237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6244336151766184287717965 2341626056912319107894237)
                  ·
                    refine ⟨878109771342119665460339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341626056912319107894237 878109771342119665460339)
                    ·
                      rfl

theorem cell22_2565169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_2565169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565169 prefixEnd_2565169 := by exact prefixLift 2565169
  have htrace : WordTrace (prefixWord ++ tailWord_2565169) baseStart_2565169 baseEnd_2565169 := by
    simpa [prefixWord, tailWord_2565169, baseEnd_2565169] using wordTrace_append hprefix tailTrace_2565169
  have hstable : (prefixWord ++ tailWord_2565169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565169).length < 2 ^ (prefixWord ++ tailWord_2565169).sum := by decide
  have hdescent : baseEnd_2565169 < baseStart_2565169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565272 : List Nat := [2, 1, 2, 4, 2, 11]
def baseStart_2565272 : Nat := 118140960795 + 2565272 * 2 ^ 59
def prefixEnd_2565272 : Nat := 4983230072969 + 3 ^ 40 * 2565272 * 2
def baseEnd_2565272 : Nat := 10841296670951379384383

theorem tailTrace_2565272 : CollatzResearch.WordTrace tailWord_2565272 prefixEnd_2565272 10841296670951379384383 := by
  unfold tailWord_2565272
  simp only [CollatzResearch.WordTrace]
  refine ⟨46781578181232566211353035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62375437574976754948470713 46781578181232566211353035)
  ·
    refine ⟨70172367271848849317029553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46781578181232566211353035 70172367271848849317029553)
    ·
      refine ⟨52629275453886636987772165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70172367271848849317029553 52629275453886636987772165)
      ·
        refine ⟨9867989147603744435207281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52629275453886636987772165 9867989147603744435207281)
        ·
          refine ⟨7400991860702808326405461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9867989147603744435207281 7400991860702808326405461)
          ·
            refine ⟨10841296670951379384383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7400991860702808326405461 10841296670951379384383)
            ·
              rfl

theorem cell22_2565272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 11].length) (baseStart_2565272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565272 prefixEnd_2565272 := by exact prefixLift 2565272
  have htrace : WordTrace (prefixWord ++ tailWord_2565272) baseStart_2565272 baseEnd_2565272 := by
    simpa [prefixWord, tailWord_2565272, baseEnd_2565272] using wordTrace_append hprefix tailTrace_2565272
  have hstable : (prefixWord ++ tailWord_2565272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565272).length < 2 ^ (prefixWord ++ tailWord_2565272).sum := by decide
  have hdescent : baseEnd_2565272 < baseStart_2565272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565276 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_2565276 : Nat := 118140960795 + 2565276 * 2 ^ 59
def prefixEnd_2565276 : Nat := 4983230072969 + 3 ^ 40 * 2565276 * 2
def baseEnd_2565276 : Nat := 878146399628807053035011

theorem tailTrace_2565276 : CollatzResearch.WordTrace tailWord_2565276 prefixEnd_2565276 878146399628807053035011 := by
  unfold tailWord_2565276
  simp only [CollatzResearch.WordTrace]
  refine ⟨46781651127225320552925841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62375534836300427403901121 46781651127225320552925841)
  ·
    refine ⟨35086238345418990414694381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46781651127225320552925841 35086238345418990414694381)
    ·
      refine ⟨13157339379532121405510393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35086238345418990414694381 13157339379532121405510393)
      ·
        refine ⟨9868004534649091054132795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13157339379532121405510393 9868004534649091054132795)
        ·
          refine ⟨14802006801973636581199193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9868004534649091054132795 14802006801973636581199193)
          ·
            refine ⟨11101505101480227435899395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14802006801973636581199193 11101505101480227435899395)
            ·
              refine ⟨16652257652220341153849093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11101505101480227435899395 16652257652220341153849093)
              ·
                refine ⟨3122298309791313966346705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16652257652220341153849093 3122298309791313966346705)
                ·
                  refine ⟨2341723732343485474760029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122298309791313966346705 2341723732343485474760029)
                  ·
                    refine ⟨878146399628807053035011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341723732343485474760029 878146399628807053035011)
                    ·
                      rfl

theorem cell22_2565276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_2565276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565276 prefixEnd_2565276 := by exact prefixLift 2565276
  have htrace : WordTrace (prefixWord ++ tailWord_2565276) baseStart_2565276 baseEnd_2565276 := by
    simpa [prefixWord, tailWord_2565276, baseEnd_2565276] using wordTrace_append hprefix tailTrace_2565276
  have hstable : (prefixWord ++ tailWord_2565276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565276).length < 2 ^ (prefixWord ++ tailWord_2565276).sum := by decide
  have hdescent : baseEnd_2565276 < baseStart_2565276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565278 : List Nat := [4, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2565278 : Nat := 118140960795 + 2565278 * 2 ^ 59
def prefixEnd_2565278 : Nat := 4983230072969 + 3 ^ 40 * 2565278 * 2
def baseEnd_2565278 : Nat := 292715694756559904828335

theorem tailTrace_2565278 : CollatzResearch.WordTrace tailWord_2565278 prefixEnd_2565278 292715694756559904828335 := by
  unfold tailWord_2565278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11695421900055424430928061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62375583466962263631616325 11695421900055424430928061)
  ·
    refine ⟨4385783212520784161598023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11695421900055424430928061 4385783212520784161598023)
    ·
      refine ⟨6578674818781176242397035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4385783212520784161598023 6578674818781176242397035)
      ·
        refine ⟨9868012228171764363595553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6578674818781176242397035 9868012228171764363595553)
        ·
          refine ⟨7401009171128823272696665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9868012228171764363595553 7401009171128823272696665)
          ·
            refine ⟨5550756878346617454522499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7401009171128823272696665 5550756878346617454522499)
            ·
              refine ⟨8326135317519926181783749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5550756878346617454522499 8326135317519926181783749)
              ·
                refine ⟨1561150372034986159084453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8326135317519926181783749 1561150372034986159084453)
                ·
                  refine ⟨292715694756559904828335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561150372034986159084453 292715694756559904828335)
                  ·
                    rfl

theorem cell22_2565278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2565278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565278 prefixEnd_2565278 := by exact prefixLift 2565278
  have htrace : WordTrace (prefixWord ++ tailWord_2565278) baseStart_2565278 baseEnd_2565278 := by
    simpa [prefixWord, tailWord_2565278, baseEnd_2565278] using wordTrace_append hprefix tailTrace_2565278
  have hstable : (prefixWord ++ tailWord_2565278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565278).length < 2 ^ (prefixWord ++ tailWord_2565278).sum := by decide
  have hdescent : baseEnd_2565278 < baseStart_2565278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565314 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2565314 : Nat := 118140960795 + 2565314 * 2 ^ 59
def prefixEnd_2565314 : Nat := 4983230072969 + 3 ^ 40 * 2565314 * 2
def baseEnd_2565314 : Nat := 878159407805387620584895

theorem tailTrace_2565314 : CollatzResearch.WordTrace tailWord_2565314 prefixEnd_2565314 878159407805387620584895 := by
  unfold tailWord_2565314
  simp only [CollatzResearch.WordTrace]
  refine ⟨23391172057078243398933749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62376458818875315730489997 23391172057078243398933749)
  ·
    refine ⟨2192922380351085318650039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23391172057078243398933749 2192922380351085318650039)
    ·
      refine ⟨3289383570526627977975059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192922380351085318650039 3289383570526627977975059)
      ·
        refine ⟨4934075355789941966962589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289383570526627977975059 4934075355789941966962589)
        ·
          refine ⟨1850278258421228237610971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4934075355789941966962589 1850278258421228237610971)
          ·
            refine ⟨2775417387631842356416457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850278258421228237610971 2775417387631842356416457)
            ·
              refine ⟨2081563040723881767312343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2775417387631842356416457 2081563040723881767312343)
              ·
                refine ⟨3122344561085822650968515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081563040723881767312343 3122344561085822650968515)
                ·
                  refine ⟨4683516841628733976452773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122344561085822650968515 4683516841628733976452773)
                  ·
                    refine ⟨878159407805387620584895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4683516841628733976452773 878159407805387620584895)
                    ·
                      rfl

theorem cell22_2565314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2565314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565314 prefixEnd_2565314 := by exact prefixLift 2565314
  have htrace : WordTrace (prefixWord ++ tailWord_2565314) baseStart_2565314 baseEnd_2565314 := by
    simpa [prefixWord, tailWord_2565314, baseEnd_2565314] using wordTrace_append hprefix tailTrace_2565314
  have hstable : (prefixWord ++ tailWord_2565314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565314).length < 2 ^ (prefixWord ++ tailWord_2565314).sum := by decide
  have hdescent : baseEnd_2565314 < baseStart_2565314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565317 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 7]
def baseStart_2565317 : Nat := 118140960795 + 2565317 * 2 ^ 59
def prefixEnd_2565317 : Nat := 4983230072969 + 3 ^ 40 * 2565317 * 2
def baseEnd_2565317 : Nat := 292720144922232204253295

theorem tailTrace_2565317 : CollatzResearch.WordTrace tailWord_2565317 prefixEnd_2565317 292720144922232204253295 := by
  unfold tailWord_2565317
  simp only [CollatzResearch.WordTrace]
  refine ⟨93564797647302105108094205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62376531764868070072062803 93564797647302105108094205)
  ·
    refine ⟨35086799117738289415535327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93564797647302105108094205 35086799117738289415535327)
    ·
      refine ⟨52630198676607434123302991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35086799117738289415535327 52630198676607434123302991)
      ·
        refine ⟨78945298014911151184954487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52630198676607434123302991 78945298014911151184954487)
        ·
          refine ⟨118417947022366726777431731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78945298014911151184954487 118417947022366726777431731)
          ·
            refine ⟨177626920533550090166147597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118417947022366726777431731 177626920533550090166147597)
            ·
              refine ⟨66610095200081283812305349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177626920533550090166147597 66610095200081283812305349)
              ·
                refine ⟨12489392850015240714807253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66610095200081283812305349 12489392850015240714807253)
                ·
                  refine ⟨292720144922232204253295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12489392850015240714807253 292720144922232204253295)
                  ·
                    rfl

theorem cell22_2565317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_2565317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565317 prefixEnd_2565317 := by exact prefixLift 2565317
  have htrace : WordTrace (prefixWord ++ tailWord_2565317) baseStart_2565317 baseEnd_2565317 := by
    simpa [prefixWord, tailWord_2565317, baseEnd_2565317] using wordTrace_append hprefix tailTrace_2565317
  have hstable : (prefixWord ++ tailWord_2565317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565317).length < 2 ^ (prefixWord ++ tailWord_2565317).sum := by decide
  have hdescent : baseEnd_2565317 < baseStart_2565317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565372 : List Nat := [2, 2, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_2565372 : Nat := 118140960795 + 2565372 * 2 ^ 59
def prefixEnd_2565372 : Nat := 4983230072969 + 3 ^ 40 * 2565372 * 2
def baseEnd_2565372 : Nat := 878179262390694802634717

theorem tailTrace_2565372 : CollatzResearch.WordTrace tailWord_2565372 prefixEnd_2565372 878179262390694802634717 := by
  unfold tailWord_2565372
  simp only [CollatzResearch.WordTrace]
  refine ⟨46783401831051424750673185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62377869108068566334230913 46783401831051424750673185)
  ·
    refine ⟨35087551373288568563004889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46783401831051424750673185 35087551373288568563004889)
    ·
      refine ⟨26315663529966426422253667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35087551373288568563004889 26315663529966426422253667)
      ·
        refine ⟨39473495294949639633380501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26315663529966426422253667 39473495294949639633380501)
        ·
          refine ⟨1850320091950764357814711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39473495294949639633380501 1850320091950764357814711)
          ·
            refine ⟨2775480137926146536722067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850320091950764357814711 2775480137926146536722067)
            ·
              refine ⟨4163220206889219805083101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775480137926146536722067 4163220206889219805083101)
              ·
                refine ⟨1561207577583457426906163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4163220206889219805083101 1561207577583457426906163)
                ·
                  refine ⟨2341811366375186140359245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561207577583457426906163 2341811366375186140359245)
                  ·
                    refine ⟨878179262390694802634717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341811366375186140359245 878179262390694802634717)
                    ·
                      rfl

theorem cell22_2565372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_2565372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565372 prefixEnd_2565372 := by exact prefixLift 2565372
  have htrace : WordTrace (prefixWord ++ tailWord_2565372) baseStart_2565372 baseEnd_2565372 := by
    simpa [prefixWord, tailWord_2565372, baseEnd_2565372] using wordTrace_append hprefix tailTrace_2565372
  have hstable : (prefixWord ++ tailWord_2565372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565372).length < 2 ^ (prefixWord ++ tailWord_2565372).sum := by decide
  have hdescent : baseEnd_2565372 < baseStart_2565372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565409 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2565409 : Nat := 118140960795 + 2565409 * 2 ^ 59
def prefixEnd_2565409 : Nat := 4983230072969 + 3 ^ 40 * 2565409 * 2
def baseEnd_2565409 : Nat := 878191928246839039459603

theorem tailTrace_2565409 : CollatzResearch.WordTrace tailWord_2565409 prefixEnd_2565409 878191928246839039459603 := by
  unfold tailWord_2565409
  simp only [CollatzResearch.WordTrace]
  refine ⟨93568153162968804820443281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62378768775312536546962187 93568153162968804820443281)
  ·
    refine ⟨70176114872226603615332461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93568153162968804820443281 70176114872226603615332461)
    ·
      refine ⟨26316043077084976355749673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70176114872226603615332461 26316043077084976355749673)
      ·
        refine ⟨19737032307813732266812255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26316043077084976355749673 19737032307813732266812255)
        ·
          refine ⟨29605548461720598400218383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19737032307813732266812255 29605548461720598400218383)
          ·
            refine ⟨44408322692580897600327575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29605548461720598400218383 44408322692580897600327575)
            ·
              refine ⟨66612484038871346400491363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44408322692580897600327575 66612484038871346400491363)
              ·
                refine ⟨99918726058307019600737045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66612484038871346400491363 99918726058307019600737045)
                ·
                  refine ⟨4683690283983141543784549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99918726058307019600737045 4683690283983141543784549)
                  ·
                    refine ⟨878191928246839039459603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4683690283983141543784549 878191928246839039459603)
                    ·
                      rfl

theorem cell22_2565409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2565409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565409 prefixEnd_2565409 := by exact prefixLift 2565409
  have htrace : WordTrace (prefixWord ++ tailWord_2565409) baseStart_2565409 baseEnd_2565409 := by
    simpa [prefixWord, tailWord_2565409, baseEnd_2565409] using wordTrace_append hprefix tailTrace_2565409
  have hstable : (prefixWord ++ tailWord_2565409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565409).length < 2 ^ (prefixWord ++ tailWord_2565409).sum := by decide
  have hdescent : baseEnd_2565409 < baseStart_2565409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565426 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_2565426 : Nat := 118140960795 + 2565426 * 2 ^ 59
def prefixEnd_2565426 : Nat := 4983230072969 + 3 ^ 40 * 2565426 * 2
def baseEnd_2565426 : Nat := 878197747694256661784551

theorem tailTrace_2565426 : CollatzResearch.WordTrace tailWord_2565426 prefixEnd_2565426 878197747694256661784551 := by
  unfold tailWord_2565426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23392193300976804180953033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62379182135938144482541421 23392193300976804180953033)
  ·
    refine ⟨17544144975732603135714775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23392193300976804180953033 17544144975732603135714775)
    ·
      refine ⟨26316217463598904703572163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17544144975732603135714775 26316217463598904703572163)
      ·
        refine ⟨39474326195398357055358245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26316217463598904703572163 39474326195398357055358245)
        ·
          refine ⟨7401436161637191947879671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39474326195398357055358245 7401436161637191947879671)
          ·
            refine ⟨11102154242455787921819507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401436161637191947879671 11102154242455787921819507)
            ·
              refine ⟨16653231363683681882729261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11102154242455787921819507 16653231363683681882729261)
              ·
                refine ⟨6244961761381380706023473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16653231363683681882729261 6244961761381380706023473)
                ·
                  refine ⟨4683721321036035529517605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6244961761381380706023473 4683721321036035529517605)
                  ·
                    refine ⟨878197747694256661784551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4683721321036035529517605 878197747694256661784551)
                    ·
                      rfl

theorem cell22_2565426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_2565426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565426 prefixEnd_2565426 := by exact prefixLift 2565426
  have htrace : WordTrace (prefixWord ++ tailWord_2565426) baseStart_2565426 baseEnd_2565426 := by
    simpa [prefixWord, tailWord_2565426, baseEnd_2565426] using wordTrace_append hprefix tailTrace_2565426
  have hstable : (prefixWord ++ tailWord_2565426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565426).length < 2 ^ (prefixWord ++ tailWord_2565426).sum := by decide
  have hdescent : baseEnd_2565426 < baseStart_2565426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565454 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2565454 : Nat := 118140960795 + 2565454 * 2 ^ 59
def prefixEnd_2565454 : Nat := 4983230072969 + 3 ^ 40 * 2565454 * 2
def baseEnd_2565454 : Nat := 878207332666473922084465

theorem tailTrace_2565454 : CollatzResearch.WordTrace tailWord_2565454 prefixEnd_2565454 878207332666473922084465 := by
  unfold tailWord_2565454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11696224305975722188228927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62379862965203851670554277 11696224305975722188228927)
  ·
    refine ⟨17544336458963583282343391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11696224305975722188228927 17544336458963583282343391)
    ·
      refine ⟨26316504688445374923515087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17544336458963583282343391 26316504688445374923515087)
      ·
        refine ⟨39474757032668062385272631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26316504688445374923515087 39474757032668062385272631)
        ·
          refine ⟨59212135549002093577908947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39474757032668062385272631 59212135549002093577908947)
          ·
            refine ⟨88818203323503140366863421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59212135549002093577908947 88818203323503140366863421)
            ·
              refine ⟨33306826246313677637573783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88818203323503140366863421 33306826246313677637573783)
              ·
                refine ⟨49960239369470516456360675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33306826246313677637573783 49960239369470516456360675)
                ·
                  refine ⟨74940359054205774684541013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49960239369470516456360675 74940359054205774684541013)
                  ·
                    refine ⟨878207332666473922084465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74940359054205774684541013 878207332666473922084465)
                    ·
                      rfl

theorem cell22_2565454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2565454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565454 prefixEnd_2565454 := by exact prefixLift 2565454
  have htrace : WordTrace (prefixWord ++ tailWord_2565454) baseStart_2565454 baseEnd_2565454 := by
    simpa [prefixWord, tailWord_2565454, baseEnd_2565454] using wordTrace_append hprefix tailTrace_2565454
  have hstable : (prefixWord ++ tailWord_2565454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565454).length < 2 ^ (prefixWord ++ tailWord_2565454).sum := by decide
  have hdescent : baseEnd_2565454 < baseStart_2565454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565456 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 3, 3]
def baseStart_2565456 : Nat := 118140960795 + 2565456 * 2 ^ 59
def prefixEnd_2565456 : Nat := 4983230072969 + 3 ^ 40 * 2565456 * 2
def baseEnd_2565456 : Nat := 878208017307346583534459

theorem tailTrace_2565456 : CollatzResearch.WordTrace tailWord_2565456 prefixEnd_2565456 878208017307346583534459 := by
  unfold tailWord_2565456
  simp only [CollatzResearch.WordTrace]
  refine ⟨46784933696899265923702111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62379911595865687898269481 46784933696899265923702111)
  ·
    refine ⟨70177400545348898885553167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46784933696899265923702111 70177400545348898885553167)
    ·
      refine ⟨105266100818023348328329751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70177400545348898885553167 105266100818023348328329751)
      ·
        refine ⟨157899151227035022492494627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105266100818023348328329751 157899151227035022492494627)
        ·
          refine ⟨236848726840552533738741941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157899151227035022492494627 236848726840552533738741941)
          ·
            refine ⟨22204568141301800038007057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236848726840552533738741941 22204568141301800038007057)
            ·
              refine ⟨16653426105976350028505293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22204568141301800038007057 16653426105976350028505293)
              ·
                refine ⟨6245034789741131260689485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16653426105976350028505293 6245034789741131260689485)
                ·
                  refine ⟨2341888046152924222758557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6245034789741131260689485 2341888046152924222758557)
                  ·
                    refine ⟨878208017307346583534459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341888046152924222758557 878208017307346583534459)
                    ·
                      rfl

theorem cell22_2565456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_2565456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565456 prefixEnd_2565456 := by exact prefixLift 2565456
  have htrace : WordTrace (prefixWord ++ tailWord_2565456) baseStart_2565456 baseEnd_2565456 := by
    simpa [prefixWord, tailWord_2565456, baseEnd_2565456] using wordTrace_append hprefix tailTrace_2565456
  have hstable : (prefixWord ++ tailWord_2565456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565456).length < 2 ^ (prefixWord ++ tailWord_2565456).sum := by decide
  have hdescent : baseEnd_2565456 < baseStart_2565456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565490 : List Nat := [3, 2, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_2565490 : Nat := 118140960795 + 2565490 * 2 ^ 59
def prefixEnd_2565490 : Nat := 4983230072969 + 3 ^ 40 * 2565490 * 2
def baseEnd_2565490 : Nat := 878219656202181828184355

theorem tailTrace_2565490 : CollatzResearch.WordTrace tailWord_2565490 prefixEnd_2565490 878219656202181828184355 := by
  unfold tailWord_2565490
  simp only [CollatzResearch.WordTrace]
  refine ⟨23392776868918838913535481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62380738317116903769427949 23392776868918838913535481)
  ·
    refine ⟨17544582651689129185151611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23392776868918838913535481 17544582651689129185151611)
    ·
      refine ⟨26316873977533693777727417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17544582651689129185151611 26316873977533693777727417)
      ·
        refine ⟨19737655483150270333295563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26316873977533693777727417 19737655483150270333295563)
        ·
          refine ⟨29606483224725405499943345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19737655483150270333295563 29606483224725405499943345)
          ·
            refine ⟨22204862418544054124957509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29606483224725405499943345 22204862418544054124957509)
            ·
              refine ⟨4163411703477010148429533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22204862418544054124957509 4163411703477010148429533)
              ·
                refine ⟨1561279388803878805661075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4163411703477010148429533 1561279388803878805661075)
                ·
                  refine ⟨2341919083205818208491613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561279388803878805661075 2341919083205818208491613)
                  ·
                    refine ⟨878219656202181828184355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341919083205818208491613 878219656202181828184355)
                    ·
                      rfl

theorem cell22_2565490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_2565490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565490 prefixEnd_2565490 := by exact prefixLift 2565490
  have htrace : WordTrace (prefixWord ++ tailWord_2565490) baseStart_2565490 baseEnd_2565490 := by
    simpa [prefixWord, tailWord_2565490, baseEnd_2565490] using wordTrace_append hprefix tailTrace_2565490
  have hstable : (prefixWord ++ tailWord_2565490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565490).length < 2 ^ (prefixWord ++ tailWord_2565490).sum := by decide
  have hdescent : baseEnd_2565490 < baseStart_2565490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565533 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2565533 : Nat := 118140960795 + 2565533 * 2 ^ 59
def prefixEnd_2565533 : Nat := 4983230072969 + 3 ^ 40 * 2565533 * 2
def baseEnd_2565533 : Nat := 878234375980944049359223

theorem tailTrace_2565533 : CollatzResearch.WordTrace tailWord_2565533 prefixEnd_2565533 878234375980944049359223 := by
  unfold tailWord_2565533
  simp only [CollatzResearch.WordTrace]
  refine ⟨93572675814519573997957253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62381783876346382665304835 93572675814519573997957253)
  ·
    refine ⟨17544876715222420124616985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93572675814519573997957253 17544876715222420124616985)
    ·
      refine ⟨13158657536416815093462739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17544876715222420124616985 13158657536416815093462739)
      ·
        refine ⟨19737986304625222640194109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13158657536416815093462739 19737986304625222640194109)
        ·
          refine ⟨7401744864234458490072791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19737986304625222640194109 7401744864234458490072791)
          ·
            refine ⟨11102617296351687735109187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401744864234458490072791 11102617296351687735109187)
            ·
              refine ⟨16653925944527531602663781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11102617296351687735109187 16653925944527531602663781)
              ·
                refine ⟨3122611114598912175499459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16653925944527531602663781 3122611114598912175499459)
                ·
                  refine ⟨4683916671898368263249189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122611114598912175499459 4683916671898368263249189)
                  ·
                    refine ⟨878234375980944049359223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4683916671898368263249189 878234375980944049359223)
                    ·
                      rfl

theorem cell22_2565533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2565533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565533 prefixEnd_2565533 := by exact prefixLift 2565533
  have htrace : WordTrace (prefixWord ++ tailWord_2565533) baseStart_2565533 baseEnd_2565533 := by
    simpa [prefixWord, tailWord_2565533, baseEnd_2565533] using wordTrace_append hprefix tailTrace_2565533
  have hstable : (prefixWord ++ tailWord_2565533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565533).length < 2 ^ (prefixWord ++ tailWord_2565533).sum := by decide
  have hdescent : baseEnd_2565533 < baseStart_2565533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565548 : List Nat := [2, 2, 1, 1, 1, 1, 7, 3, 4]
def baseStart_2565548 : Nat := 118140960795 + 2565548 * 2 ^ 59
def prefixEnd_2565548 : Nat := 4983230072969 + 3 ^ 40 * 2565548 * 2
def baseEnd_2565548 : Nat := 292746503595829670078059

theorem tailTrace_2565548 : CollatzResearch.WordTrace tailWord_2565548 prefixEnd_2565548 292746503595829670078059 := by
  unfold tailWord_2565548
  simp only [CollatzResearch.WordTrace]
  refine ⟨46786611454732615779876649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62382148606310154373168865 46786611454732615779876649)
  ·
    refine ⟨35089958591049461834907487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46786611454732615779876649 35089958591049461834907487)
    ·
      refine ⟨52634937886574192752361231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35089958591049461834907487 52634937886574192752361231)
      ·
        refine ⟨78952406829861289128541847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52634937886574192752361231 78952406829861289128541847)
        ·
          refine ⟨118428610244791933692812771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78952406829861289128541847 118428610244791933692812771)
          ·
            refine ⟨177642915367187900539219157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118428610244791933692812771 177642915367187900539219157)
            ·
              refine ⟨4163505828918466418887949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 177642915367187900539219157 4163505828918466418887949)
              ·
                refine ⟨1561314685844424907082981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4163505828918466418887949 1561314685844424907082981)
                ·
                  refine ⟨292746503595829670078059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561314685844424907082981 292746503595829670078059)
                  ·
                    rfl

theorem cell22_2565548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_2565548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565548 prefixEnd_2565548 := by exact prefixLift 2565548
  have htrace : WordTrace (prefixWord ++ tailWord_2565548) baseStart_2565548 baseEnd_2565548 := by
    simpa [prefixWord, tailWord_2565548, baseEnd_2565548] using wordTrace_append hprefix tailTrace_2565548
  have hstable : (prefixWord ++ tailWord_2565548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565548).length < 2 ^ (prefixWord ++ tailWord_2565548).sum := by decide
  have hdescent : baseEnd_2565548 < baseStart_2565548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565565 : List Nat := [1, 4, 1, 2, 2, 1, 5, 2, 4]
def baseStart_2565565 : Nat := 118140960795 + 2565565 * 2 ^ 59
def prefixEnd_2565565 : Nat := 4983230072969 + 3 ^ 40 * 2565565 * 2
def baseEnd_2565565 : Nat := 292748443411635544186375

theorem tailTrace_2565565 : CollatzResearch.WordTrace tailWord_2565565 prefixEnd_2565565 292748443411635544186375 := by
  unfold tailWord_2565565
  simp only [CollatzResearch.WordTrace]
  refine ⟨93573842950403643463122149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62382561966935762308748099 93573842950403643463122149)
  ·
    refine ⟨17545095553200683149335403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93573842950403643463122149 17545095553200683149335403)
    ·
      refine ⟨26317643329801024724003105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17545095553200683149335403 26317643329801024724003105)
      ·
        refine ⟨19738232497350768543002329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26317643329801024724003105 19738232497350768543002329)
        ·
          refine ⟨14803674373013076407251747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19738232497350768543002329 14803674373013076407251747)
          ·
            refine ⟨22205511559519614610877621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14803674373013076407251747 22205511559519614610877621)
            ·
              refine ⟨2081766708704963869769777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22205511559519614610877621 2081766708704963869769777)
              ·
                refine ⟨1561325031528722902327333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2081766708704963869769777 1561325031528722902327333)
                ·
                  refine ⟨292748443411635544186375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561325031528722902327333 292748443411635544186375)
                  ·
                    rfl

theorem cell22_2565565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_2565565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565565 prefixEnd_2565565 := by exact prefixLift 2565565
  have htrace : WordTrace (prefixWord ++ tailWord_2565565) baseStart_2565565 baseEnd_2565565 := by
    simpa [prefixWord, tailWord_2565565, baseEnd_2565565] using wordTrace_append hprefix tailTrace_2565565
  have hstable : (prefixWord ++ tailWord_2565565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565565).length < 2 ^ (prefixWord ++ tailWord_2565565).sum := by decide
  have hdescent : baseEnd_2565565 < baseStart_2565565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565576 : List Nat := [2, 1, 3, 1, 3, 1, 4, 7]
def baseStart_2565576 : Nat := 118140960795 + 2565576 * 2 ^ 59
def prefixEnd_2565576 : Nat := 4983230072969 + 3 ^ 40 * 2565576 * 2
def baseEnd_2565576 : Nat := 97583232862189585614899

theorem tailTrace_2565576 : CollatzResearch.WordTrace tailWord_2565576 prefixEnd_2565576 97583232862189585614899 := by
  unfold tailWord_2565576
  simp only [CollatzResearch.WordTrace]
  refine ⟨46787122076681896170886291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62382829435575861561181721 46787122076681896170886291)
  ·
    refine ⟨70180683115022844256329437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46787122076681896170886291 70180683115022844256329437)
    ·
      refine ⟨26317756168133566596123539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70180683115022844256329437 26317756168133566596123539)
      ·
        refine ⟨39476634252200349894185309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26317756168133566596123539 39476634252200349894185309)
        ·
          refine ⟨14803737844575131210319491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39476634252200349894185309 14803737844575131210319491)
          ·
            refine ⟨22205606766862696815479237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14803737844575131210319491 22205606766862696815479237)
            ·
              refine ⟨4163551268786755652902357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22205606766862696815479237 4163551268786755652902357)
              ·
                refine ⟨97583232862189585614899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4163551268786755652902357 97583232862189585614899)
                ·
                  rfl

theorem cell22_2565576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_2565576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565576 prefixEnd_2565576 := by exact prefixLift 2565576
  have htrace : WordTrace (prefixWord ++ tailWord_2565576) baseStart_2565576 baseEnd_2565576 := by
    simpa [prefixWord, tailWord_2565576, baseEnd_2565576] using wordTrace_append hprefix tailTrace_2565576
  have hstable : (prefixWord ++ tailWord_2565576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565576).length < 2 ^ (prefixWord ++ tailWord_2565576).sum := by decide
  have hdescent : baseEnd_2565576 < baseStart_2565576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565580 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_2565580 : Nat := 118140960795 + 2565580 * 2 ^ 59
def prefixEnd_2565580 : Nat := 4983230072969 + 3 ^ 40 * 2565580 * 2
def baseEnd_2565580 : Nat := 878250465041451593434079

theorem tailTrace_2565580 : CollatzResearch.WordTrace tailWord_2565580 prefixEnd_2565580 878250465041451593434079 := by
  unfold tailWord_2565580
  simp only [CollatzResearch.WordTrace]
  refine ⟨46787195022674650512459097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62382926696899534016612129 46787195022674650512459097)
  ·
    refine ⟨35090396267005987884344323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46787195022674650512459097 35090396267005987884344323)
    ·
      refine ⟨52635594400508981826516485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35090396267005987884344323 52635594400508981826516485)
      ·
        refine ⟨9869173950095434092471841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52635594400508981826516485 9869173950095434092471841)
        ·
          refine ⟨7401880462571575569353881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9869173950095434092471841 7401880462571575569353881)
          ·
            refine ⟨5551410346928681677015411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7401880462571575569353881 5551410346928681677015411)
            ·
              refine ⟨8327115520393022515523117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551410346928681677015411 8327115520393022515523117)
              ·
                refine ⟨3122668320147383443321169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8327115520393022515523117 3122668320147383443321169)
                ·
                  refine ⟨2342001240110537582490877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122668320147383443321169 2342001240110537582490877)
                  ·
                    refine ⟨878250465041451593434079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342001240110537582490877 878250465041451593434079)
                    ·
                      rfl

theorem cell22_2565580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_2565580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565580 prefixEnd_2565580 := by exact prefixLift 2565580
  have htrace : WordTrace (prefixWord ++ tailWord_2565580) baseStart_2565580 baseEnd_2565580 := by
    simpa [prefixWord, tailWord_2565580, baseEnd_2565580] using wordTrace_append hprefix tailTrace_2565580
  have hstable : (prefixWord ++ tailWord_2565580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565580).length < 2 ^ (prefixWord ++ tailWord_2565580).sum := by decide
  have hdescent : baseEnd_2565580 < baseStart_2565580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565672 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 5]
def baseStart_2565672 : Nat := 118140960795 + 2565672 * 2 ^ 59
def prefixEnd_2565672 : Nat := 4983230072969 + 3 ^ 40 * 2565672 * 2
def baseEnd_2565672 : Nat := 292760652840531340044599

theorem tailTrace_2565672 : CollatzResearch.WordTrace tailWord_2565672 prefixEnd_2565672 292760652840531340044599 := by
  unfold tailWord_2565672
  simp only [CollatzResearch.WordTrace]
  refine ⟨46788872780508000368633635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62385163707344000491511513 46788872780508000368633635)
  ·
    refine ⟨70183309170762000552950453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46788872780508000368633635 70183309170762000552950453)
    ·
      refine ⟨6579685234758937551839105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70183309170762000552950453 6579685234758937551839105)
      ·
        refine ⟨4934763926069203163879329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6579685234758937551839105 4934763926069203163879329)
        ·
          refine ⟨3701072944551902372909497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4934763926069203163879329 3701072944551902372909497)
          ·
            refine ⟨2775804708413926779682123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3701072944551902372909497 2775804708413926779682123)
            ·
              refine ⟨4163707062620890169523185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775804708413926779682123 4163707062620890169523185)
              ·
                refine ⟨3122780296965667627142389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4163707062620890169523185 3122780296965667627142389)
                ·
                  refine ⟨292760652840531340044599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3122780296965667627142389 292760652840531340044599)
                  ·
                    rfl

theorem cell22_2565672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_2565672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565672 prefixEnd_2565672 := by exact prefixLift 2565672
  have htrace : WordTrace (prefixWord ++ tailWord_2565672) baseStart_2565672 baseEnd_2565672 := by
    simpa [prefixWord, tailWord_2565672, baseEnd_2565672] using wordTrace_append hprefix tailTrace_2565672
  have hstable : (prefixWord ++ tailWord_2565672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565672).length < 2 ^ (prefixWord ++ tailWord_2565672).sum := by decide
  have hdescent : baseEnd_2565672 < baseStart_2565672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565683 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 6]
def baseStart_2565683 : Nat := 118140960795 + 2565683 * 2 ^ 59
def prefixEnd_2565683 : Nat := 4983230072969 + 3 ^ 40 * 2565683 * 2
def baseEnd_2565683 : Nat := 292761908015464552702921

theorem tailTrace_2565683 : CollatzResearch.WordTrace tailWord_2565683 prefixEnd_2565683 292761908015464552702921 := by
  unfold tailWord_2565683
  simp only [CollatzResearch.WordTrace]
  refine ⟨93578146763976149615917703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62385431175984099743945135 93578146763976149615917703)
  ·
    refine ⟨140367220145964224423876555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93578146763976149615917703 140367220145964224423876555)
    ·
      refine ⟨210550830218946336635814833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140367220145964224423876555 210550830218946336635814833)
      ·
        refine ⟨157913122664209752476861125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210550830218946336635814833 157913122664209752476861125)
        ·
          refine ⟨29608710499539328589411461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157913122664209752476861125 29608710499539328589411461)
          ·
            refine ⟨5551633218663624110514649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29608710499539328589411461 5551633218663624110514649)
            ·
              refine ⟨4163724913997718082885987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551633218663624110514649 4163724913997718082885987)
              ·
                refine ⟨6245587370996577124328981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163724913997718082885987 6245587370996577124328981)
                ·
                  refine ⟨292761908015464552702921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6245587370996577124328981 292761908015464552702921)
                  ·
                    rfl

theorem cell22_2565683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 6].length) (baseStart_2565683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565683 prefixEnd_2565683 := by exact prefixLift 2565683
  have htrace : WordTrace (prefixWord ++ tailWord_2565683) baseStart_2565683 baseEnd_2565683 := by
    simpa [prefixWord, tailWord_2565683, baseEnd_2565683] using wordTrace_append hprefix tailTrace_2565683
  have hstable : (prefixWord ++ tailWord_2565683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565683).length < 2 ^ (prefixWord ++ tailWord_2565683).sum := by decide
  have hdescent : baseEnd_2565683 < baseStart_2565683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565713 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_2565713 : Nat := 118140960795 + 2565713 * 2 ^ 59
def prefixEnd_2565713 : Nat := 4983230072969 + 3 ^ 40 * 2565713 * 2
def baseEnd_2565713 : Nat := 878295993659483579858671

theorem tailTrace_2565713 : CollatzResearch.WordTrace tailWord_2565713 prefixEnd_2565713 878295993659483579858671 := by
  unfold tailWord_2565713
  simp only [CollatzResearch.WordTrace]
  refine ⟨93579240953867464739509793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62386160635911643159673195 93579240953867464739509793)
  ·
    refine ⟨70184430715400598554632345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93579240953867464739509793 70184430715400598554632345)
    ·
      refine ⟨52638323036550448915974259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70184430715400598554632345 52638323036550448915974259)
      ·
        refine ⟨78957484554825673373961389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52638323036550448915974259 78957484554825673373961389)
        ·
          refine ⟨29609056708059627515235521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78957484554825673373961389 29609056708059627515235521)
          ·
            refine ⟨22206792531044720636426641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29609056708059627515235521 22206792531044720636426641)
            ·
              refine ⟨16655094398283540477319981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22206792531044720636426641 16655094398283540477319981)
              ·
                refine ⟨6245660399356327678994993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16655094398283540477319981 6245660399356327678994993)
                ·
                  refine ⟨4684245299517245759246245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6245660399356327678994993 4684245299517245759246245)
                  ·
                    refine ⟨878295993659483579858671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4684245299517245759246245 878295993659483579858671)
                    ·
                      rfl

theorem cell22_2565713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_2565713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565713 prefixEnd_2565713 := by exact prefixLift 2565713
  have htrace : WordTrace (prefixWord ++ tailWord_2565713) baseStart_2565713 baseEnd_2565713 := by
    simpa [prefixWord, tailWord_2565713, baseEnd_2565713] using wordTrace_append hprefix tailTrace_2565713
  have hstable : (prefixWord ++ tailWord_2565713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565713).length < 2 ^ (prefixWord ++ tailWord_2565713).sum := by decide
  have hdescent : baseEnd_2565713 < baseStart_2565713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565749 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2565749 : Nat := 118140960795 + 2565749 * 2 ^ 59
def prefixEnd_2565749 : Nat := 4983230072969 + 3 ^ 40 * 2565749 * 2
def baseEnd_2565749 : Nat := 878308317195191485958561

theorem tailTrace_2565749 : CollatzResearch.WordTrace tailWord_2565749 prefixEnd_2565749 878308317195191485958561 := by
  unfold tailWord_2565749
  simp only [CollatzResearch.WordTrace]
  refine ⟨93580553981737042887820301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62387035987824695258546867 93580553981737042887820301)
  ·
    refine ⟨35092707743151391082932613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93580553981737042887820301 35092707743151391082932613)
    ·
      refine ⟨6579882701840885828049865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35092707743151391082932613 6579882701840885828049865)
      ·
        refine ⟨4934912026380664371037399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6579882701840885828049865 4934912026380664371037399)
        ·
          refine ⟨7402368039570996556556099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934912026380664371037399 7402368039570996556556099)
          ·
            refine ⟨11103552059356494834834149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402368039570996556556099 11103552059356494834834149)
            ·
              refine ⟨2081916011129342781531403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11103552059356494834834149 2081916011129342781531403)
              ·
                refine ⟨3122874016694014172297105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081916011129342781531403 3122874016694014172297105)
                ·
                  refine ⟨2342155512520510629222829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122874016694014172297105 2342155512520510629222829)
                  ·
                    refine ⟨878308317195191485958561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342155512520510629222829 878308317195191485958561)
                    ·
                      rfl

theorem cell22_2565749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2565749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565749 prefixEnd_2565749 := by exact prefixLift 2565749
  have htrace : WordTrace (prefixWord ++ tailWord_2565749) baseStart_2565749 baseEnd_2565749 := by
    simpa [prefixWord, tailWord_2565749, baseEnd_2565749] using wordTrace_append hprefix tailTrace_2565749
  have hstable : (prefixWord ++ tailWord_2565749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565749).length < 2 ^ (prefixWord ++ tailWord_2565749).sum := by decide
  have hdescent : baseEnd_2565749 < baseStart_2565749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565805 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2565805 : Nat := 118140960795 + 2565805 * 2 ^ 59
def prefixEnd_2565805 : Nat := 4983230072969 + 3 ^ 40 * 2565805 * 2
def baseEnd_2565805 : Nat := 878327487139626006558389

theorem tailTrace_2565805 : CollatzResearch.WordTrace tailWord_2565805 prefixEnd_2565805 878327487139626006558389 := by
  unfold tailWord_2565805
  simp only [CollatzResearch.WordTrace]
  refine ⟨93582596469534164451858869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62388397646356109634572579 93582596469534164451858869)
  ·
    refine ⟨8773368419018827917361769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93582596469534164451858869 8773368419018827917361769)
    ·
      refine ⟨6580026314264120938021327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8773368419018827917361769 6580026314264120938021327)
      ·
        refine ⟨9870039471396181407031991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6580026314264120938021327 9870039471396181407031991)
        ·
          refine ⟨14805059207094272110547987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9870039471396181407031991 14805059207094272110547987)
          ·
            refine ⟨22207588810641408165821981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14805059207094272110547987 22207588810641408165821981)
            ·
              refine ⟨8327845803990528062183243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22207588810641408165821981 8327845803990528062183243)
              ·
                refine ⟨12491768705985792093274865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327845803990528062183243 12491768705985792093274865)
                ·
                  refine ⟨9368826529489344069956149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12491768705985792093274865 9368826529489344069956149)
                  ·
                    refine ⟨878327487139626006558389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9368826529489344069956149 878327487139626006558389)
                    ·
                      rfl

theorem cell22_2565805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2565805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565805 prefixEnd_2565805 := by exact prefixLift 2565805
  have htrace : WordTrace (prefixWord ++ tailWord_2565805) baseStart_2565805 baseEnd_2565805 := by
    simpa [prefixWord, tailWord_2565805, baseEnd_2565805] using wordTrace_append hprefix tailTrace_2565805
  have hstable : (prefixWord ++ tailWord_2565805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565805).length < 2 ^ (prefixWord ++ tailWord_2565805).sum := by decide
  have hdescent : baseEnd_2565805 < baseStart_2565805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565818 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_2565818 : Nat := 118140960795 + 2565818 * 2 ^ 59
def prefixEnd_2565818 : Nat := 4983230072969 + 3 ^ 40 * 2565818 * 2
def baseEnd_2565818 : Nat := 292777312435099435327783

theorem tailTrace_2565818 : CollatzResearch.WordTrace tailWord_2565818 prefixEnd_2565818 292777312435099435327783 := by
  unfold tailWord_2565818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23395767654621766918020527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62388713745658045114721405 23395767654621766918020527)
  ·
    refine ⟨35093651481932650377030791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23395767654621766918020527 35093651481932650377030791)
    ·
      refine ⟨52640477222898975565546187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35093651481932650377030791 52640477222898975565546187)
      ·
        refine ⟨78960715834348463348319281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52640477222898975565546187 78960715834348463348319281)
        ·
          refine ⟨59220536875761347511239461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78960715834348463348319281 59220536875761347511239461)
          ·
            refine ⟨11103850664205252658357399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59220536875761347511239461 11103850664205252658357399)
            ·
              refine ⟨16655775996307878987536099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11103850664205252658357399 16655775996307878987536099)
              ·
                refine ⟨24983663994461818481304149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16655775996307878987536099 24983663994461818481304149)
                ·
                  refine ⟨292777312435099435327783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24983663994461818481304149 292777312435099435327783)
                  ·
                    rfl

theorem cell22_2565818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_2565818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565818 prefixEnd_2565818 := by exact prefixLift 2565818
  have htrace : WordTrace (prefixWord ++ tailWord_2565818) baseStart_2565818 baseEnd_2565818 := by
    simpa [prefixWord, tailWord_2565818, baseEnd_2565818] using wordTrace_append hprefix tailTrace_2565818
  have hstable : (prefixWord ++ tailWord_2565818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565818).length < 2 ^ (prefixWord ++ tailWord_2565818).sum := by decide
  have hdescent : baseEnd_2565818 < baseStart_2565818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565820 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_2565820 : Nat := 118140960795 + 2565820 * 2 ^ 59
def prefixEnd_2565820 : Nat := 4983230072969 + 3 ^ 40 * 2565820 * 2
def baseEnd_2565820 : Nat := 878332621946170967433343

theorem tailTrace_2565820 : CollatzResearch.WordTrace tailWord_2565820 prefixEnd_2565820 878332621946170967433343 := by
  unfold tailWord_2565820
  simp only [CollatzResearch.WordTrace]
  refine ⟨46791571782239911006827457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62388762376319881342436609 46791571782239911006827457)
  ·
    refine ⟨35093678836679933255120593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46791571782239911006827457 35093678836679933255120593)
    ·
      refine ⟨26320259127509949941340445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35093678836679933255120593 26320259127509949941340445)
      ·
        refine ⟨9870097172816231228002667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26320259127509949941340445 9870097172816231228002667)
        ·
          refine ⟨14805145759224346842004001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9870097172816231228002667 14805145759224346842004001)
          ·
            refine ⟨11103859319418260131503001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14805145759224346842004001 11103859319418260131503001)
            ·
              refine ⟨8327894489563695098627251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11103859319418260131503001 8327894489563695098627251)
              ·
                refine ⟨12491841734345542647940877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327894489563695098627251 12491841734345542647940877)
                ·
                  refine ⟨4684440650379578492977829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12491841734345542647940877 4684440650379578492977829)
                  ·
                    refine ⟨878332621946170967433343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4684440650379578492977829 878332621946170967433343)
                    ·
                      rfl

theorem cell22_2565820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_2565820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565820 prefixEnd_2565820 := by exact prefixLift 2565820
  have htrace : WordTrace (prefixWord ++ tailWord_2565820) baseStart_2565820 baseEnd_2565820 := by
    simpa [prefixWord, tailWord_2565820, baseEnd_2565820] using wordTrace_append hprefix tailTrace_2565820
  have hstable : (prefixWord ++ tailWord_2565820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565820).length < 2 ^ (prefixWord ++ tailWord_2565820).sum := by decide
  have hdescent : baseEnd_2565820 < baseStart_2565820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565886 : List Nat := [4, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_2565886 : Nat := 118140960795 + 2565886 * 2 ^ 59
def prefixEnd_2565886 : Nat := 4983230072969 + 3 ^ 40 * 2565886 * 2
def baseEnd_2565886 : Nat := 292785071698322931761047

theorem tailTrace_2565886 : CollatzResearch.WordTrace tailWord_2565886 prefixEnd_2565886 292785071698322931761047 := by
  unfold tailWord_2565886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11698193847780089410694689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62390367188160476857038341 11698193847780089410694689)
  ·
    refine ⟨8773645385835067058021017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11698193847780089410694689 8773645385835067058021017)
    ·
      refine ⟨6580234039376300293515763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8773645385835067058021017 6580234039376300293515763)
      ·
        refine ⟨9870351059064450440273645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6580234039376300293515763 9870351059064450440273645)
        ·
          refine ⟨3701381647149168915102617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9870351059064450440273645 3701381647149168915102617)
          ·
            refine ⟨2776036235361876686326963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3701381647149168915102617 2776036235361876686326963)
            ·
              refine ⟨4164054353042815029490445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776036235361876686326963 4164054353042815029490445)
              ·
                refine ⟨1561520382391055636058917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4164054353042815029490445 1561520382391055636058917)
                ·
                  refine ⟨292785071698322931761047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561520382391055636058917 292785071698322931761047)
                  ·
                    rfl

theorem cell22_2565886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_2565886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565886 prefixEnd_2565886 := by exact prefixLift 2565886
  have htrace : WordTrace (prefixWord ++ tailWord_2565886) baseStart_2565886 baseEnd_2565886 := by
    simpa [prefixWord, tailWord_2565886, baseEnd_2565886] using wordTrace_append hprefix tailTrace_2565886
  have hstable : (prefixWord ++ tailWord_2565886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565886).length < 2 ^ (prefixWord ++ tailWord_2565886).sum := by decide
  have hdescent : baseEnd_2565886 < baseStart_2565886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565893 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_2565893 : Nat := 118140960795 + 2565893 * 2 ^ 59
def prefixEnd_2565893 : Nat := 4983230072969 + 3 ^ 40 * 2565893 * 2
def baseEnd_2565893 : Nat := 878357611338023110358119

theorem tailTrace_2565893 : CollatzResearch.WordTrace tailWord_2565893 prefixEnd_2565893 878357611338023110358119 := by
  unfold tailWord_2565893
  simp only [CollatzResearch.WordTrace]
  refine ⟨93585806093215355481062333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62390537395476903654041555 93585806093215355481062333)
  ·
    refine ⟨35094677284955758305398375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93585806093215355481062333 35094677284955758305398375)
    ·
      refine ⟨52642015927433637458097563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35094677284955758305398375 52642015927433637458097563)
      ·
        refine ⟨78963023891150456187146345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52642015927433637458097563 78963023891150456187146345)
        ·
          refine ⟨59222267918362842140359759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78963023891150456187146345 59222267918362842140359759)
          ·
            refine ⟨88833401877544263210539639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59222267918362842140359759 88833401877544263210539639)
            ·
              refine ⟨133250102816316394815809459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88833401877544263210539639 133250102816316394815809459)
              ·
                refine ⟨199875154224474592223714189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133250102816316394815809459 199875154224474592223714189)
                ·
                  refine ⟨74953182834177972083892821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199875154224474592223714189 74953182834177972083892821)
                  ·
                    refine ⟨878357611338023110358119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74953182834177972083892821 878357611338023110358119)
                    ·
                      rfl

theorem cell22_2565893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_2565893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565893 prefixEnd_2565893 := by exact prefixLift 2565893
  have htrace : WordTrace (prefixWord ++ tailWord_2565893) baseStart_2565893 baseEnd_2565893 := by
    simpa [prefixWord, tailWord_2565893, baseEnd_2565893] using wordTrace_append hprefix tailTrace_2565893
  have hstable : (prefixWord ++ tailWord_2565893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565893).length < 2 ^ (prefixWord ++ tailWord_2565893).sum := by decide
  have hdescent : baseEnd_2565893 < baseStart_2565893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565912 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 3, 3]
def baseStart_2565912 : Nat := 118140960795 + 2565912 * 2 ^ 59
def prefixEnd_2565912 : Nat := 4983230072969 + 3 ^ 40 * 2565912 * 2
def baseEnd_2565912 : Nat := 878364115426313394133061

theorem tailTrace_2565912 : CollatzResearch.WordTrace tailWord_2565912 prefixEnd_2565912 878364115426313394133061 := by
  unfold tailWord_2565912
  simp only [CollatzResearch.WordTrace]
  refine ⟨46793249540073260863001995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62390999386764347817335993 46793249540073260863001995)
  ·
    refine ⟨70189874310109891294502993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46793249540073260863001995 70189874310109891294502993)
    ·
      refine ⟨52642405732582418470877245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70189874310109891294502993 52642405732582418470877245)
      ·
        refine ⟨19740902149718406926578967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52642405732582418470877245 19740902149718406926578967)
        ·
          refine ⟨29611353224577610389868451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19740902149718406926578967 29611353224577610389868451)
          ·
            refine ⟨44417029836866415584802677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29611353224577610389868451 44417029836866415584802677)
            ·
              refine ⟨4164096547206226461075251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44417029836866415584802677 4164096547206226461075251)
              ·
                refine ⟨6246144820809339691612877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164096547206226461075251 6246144820809339691612877)
                ·
                  refine ⟨2342304307803502384354829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6246144820809339691612877 2342304307803502384354829)
                  ·
                    refine ⟨878364115426313394133061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342304307803502384354829 878364115426313394133061)
                    ·
                      rfl

theorem cell22_2565912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_2565912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565912 prefixEnd_2565912 := by exact prefixLift 2565912
  have htrace : WordTrace (prefixWord ++ tailWord_2565912) baseStart_2565912 baseEnd_2565912 := by
    simpa [prefixWord, tailWord_2565912, baseEnd_2565912] using wordTrace_append hprefix tailTrace_2565912
  have hstable : (prefixWord ++ tailWord_2565912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565912).length < 2 ^ (prefixWord ++ tailWord_2565912).sum := by decide
  have hdescent : baseEnd_2565912 < baseStart_2565912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565918 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2565918 : Nat := 118140960795 + 2565918 * 2 ^ 59
def prefixEnd_2565918 : Nat := 4983230072969 + 3 ^ 40 * 2565918 * 2
def baseEnd_2565918 : Nat := 878366169348931378483043

theorem tailTrace_2565918 : CollatzResearch.WordTrace tailWord_2565918 prefixEnd_2565918 878366169348931378483043 := by
  unfold tailWord_2565918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11698339739765598093840301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62391145278749856500481605 11698339739765598093840301)
  ·
    refine ⟨4386877402412099285190113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11698339739765598093840301 4386877402412099285190113)
    ·
      refine ⟨3290158051809074463892585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4386877402412099285190113 3290158051809074463892585)
      ·
        refine ⟨2467618538856805847919439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3290158051809074463892585 2467618538856805847919439)
        ·
          refine ⟨3701427808285208771879159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467618538856805847919439 3701427808285208771879159)
          ·
            refine ⟨5552141712427813157818739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701427808285208771879159 5552141712427813157818739)
            ·
              refine ⟨8328212568641719736728109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552141712427813157818739 8328212568641719736728109)
              ·
                refine ⟨3123079713240644901273041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8328212568641719736728109 3123079713240644901273041)
                ·
                  refine ⟨2342309784930483675954781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3123079713240644901273041 2342309784930483675954781)
                  ·
                    refine ⟨878366169348931378483043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342309784930483675954781 878366169348931378483043)
                    ·
                      rfl

theorem cell22_2565918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2565918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565918 prefixEnd_2565918 := by exact prefixLift 2565918
  have htrace : WordTrace (prefixWord ++ tailWord_2565918) baseStart_2565918 baseEnd_2565918 := by
    simpa [prefixWord, tailWord_2565918, baseEnd_2565918] using wordTrace_append hprefix tailTrace_2565918
  have hstable : (prefixWord ++ tailWord_2565918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565918).length < 2 ^ (prefixWord ++ tailWord_2565918).sum := by decide
  have hdescent : baseEnd_2565918 < baseStart_2565918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565972 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2565972 : Nat := 118140960795 + 2565972 * 2 ^ 59
def prefixEnd_2565972 : Nat := 4983230072969 + 3 ^ 40 * 2565972 * 2
def baseEnd_2565972 : Nat := 878384654652493237632877

theorem tailTrace_2565972 : CollatzResearch.WordTrace tailWord_2565972 prefixEnd_2565972 878384654652493237632877 := by
  unfold tailWord_2565972
  simp only [CollatzResearch.WordTrace]
  refine ⟨46794343729964575986594085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62392458306619434648792113 46794343729964575986594085)
  ·
    refine ⟨8773939449368357997486391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46794343729964575986594085 8773939449368357997486391)
    ·
      refine ⟨13160909174052536996229587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8773939449368357997486391 13160909174052536996229587)
      ·
        refine ⟨19741363761078805494344381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13160909174052536996229587 19741363761078805494344381)
        ·
          refine ⟨7403011410404552060379143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19741363761078805494344381 7403011410404552060379143)
          ·
            refine ⟨11104517115606828090568715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7403011410404552060379143 11104517115606828090568715)
            ·
              refine ⟨16656775673410242135853073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11104517115606828090568715 16656775673410242135853073)
              ·
                refine ⟨12492581755057681601889805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16656775673410242135853073 12492581755057681601889805)
                ·
                  refine ⟨4684718158146630600708677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12492581755057681601889805 4684718158146630600708677)
                  ·
                    refine ⟨878384654652493237632877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4684718158146630600708677 878384654652493237632877)
                    ·
                      rfl

theorem cell22_2565972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2565972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565972 prefixEnd_2565972 := by exact prefixLift 2565972
  have htrace : WordTrace (prefixWord ++ tailWord_2565972) baseStart_2565972 baseEnd_2565972 := by
    simpa [prefixWord, tailWord_2565972, baseEnd_2565972] using wordTrace_append hprefix tailTrace_2565972
  have hstable : (prefixWord ++ tailWord_2565972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565972).length < 2 ^ (prefixWord ++ tailWord_2565972).sum := by decide
  have hdescent : baseEnd_2565972 < baseStart_2565972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2565987 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 6]
def baseStart_2565987 : Nat := 118140960795 + 2565987 * 2 ^ 59
def prefixEnd_2565987 : Nat := 4983230072969 + 3 ^ 40 * 2565987 * 2
def baseEnd_2565987 : Nat := 292796596486346066169277

theorem tailTrace_2565987 : CollatzResearch.WordTrace tailWord_2565987 prefixEnd_2565987 292796596486346066169277 := by
  unfold tailWord_2565987
  simp only [CollatzResearch.WordTrace]
  refine ⟨93589234554874809534984215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62392823036583206356656143 93589234554874809534984215)
  ·
    refine ⟨140383851832312214302476323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93589234554874809534984215 140383851832312214302476323)
    ·
      refine ⟨210575777748468321453714485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140383851832312214302476323 210575777748468321453714485)
      ·
        refine ⟨19741479163918905136285733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210575777748468321453714485 19741479163918905136285733)
        ·
          refine ⟨3701527343234794713053575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19741479163918905136285733 3701527343234794713053575)
          ·
            refine ⟨5552291014852192069580363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701527343234794713053575 5552291014852192069580363)
            ·
              refine ⟨8328436522278288104370545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552291014852192069580363 8328436522278288104370545)
              ·
                refine ⟨6246327391708716078277909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8328436522278288104370545 6246327391708716078277909)
                ·
                  refine ⟨292796596486346066169277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6246327391708716078277909 292796596486346066169277)
                  ·
                    rfl

theorem cell22_2565987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 6].length) (baseStart_2565987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2565987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2565987 prefixEnd_2565987 := by exact prefixLift 2565987
  have htrace : WordTrace (prefixWord ++ tailWord_2565987) baseStart_2565987 baseEnd_2565987 := by
    simpa [prefixWord, tailWord_2565987, baseEnd_2565987] using wordTrace_append hprefix tailTrace_2565987
  have hstable : (prefixWord ++ tailWord_2565987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2565987).length < 2 ^ (prefixWord ++ tailWord_2565987).sum := by decide
  have hdescent : baseEnd_2565987 < baseStart_2565987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2565987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566002 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_2566002 : Nat := 118140960795 + 2566002 * 2 ^ 59
def prefixEnd_2566002 : Nat := 4983230072969 + 3 ^ 40 * 2566002 * 2
def baseEnd_2566002 : Nat := 878394924265583159382785

theorem tailTrace_2566002 : CollatzResearch.WordTrace tailWord_2566002 prefixEnd_2566002 878394924265583159382785 := by
  unfold tailWord_2566002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23397445412455116774195065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62393187766546978064520173 23397445412455116774195065)
  ·
    refine ⟨17548084059341337580646299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23397445412455116774195065 17548084059341337580646299)
    ·
      refine ⟨26322126089012006370969449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17548084059341337580646299 26322126089012006370969449)
      ·
        refine ⟨19741594566759004778227087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26322126089012006370969449 19741594566759004778227087)
        ·
          refine ⟨29612391850138507167340631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19741594566759004778227087 29612391850138507167340631)
          ·
            refine ⟨44418587775207760751010947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29612391850138507167340631 44418587775207760751010947)
            ·
              refine ⟨66627881662811641126516421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44418587775207760751010947 66627881662811641126516421)
              ·
                refine ⟨12492727811777182711221829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66627881662811641126516421 12492727811777182711221829)
                ·
                  refine ⟨2342386464708221758354093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12492727811777182711221829 2342386464708221758354093)
                  ·
                    refine ⟨878394924265583159382785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342386464708221758354093 878394924265583159382785)
                    ·
                      rfl

theorem cell22_2566002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_2566002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566002 prefixEnd_2566002 := by exact prefixLift 2566002
  have htrace : WordTrace (prefixWord ++ tailWord_2566002) baseStart_2566002 baseEnd_2566002 := by
    simpa [prefixWord, tailWord_2566002, baseEnd_2566002] using wordTrace_append hprefix tailTrace_2566002
  have hstable : (prefixWord ++ tailWord_2566002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566002).length < 2 ^ (prefixWord ++ tailWord_2566002).sum := by decide
  have hdescent : baseEnd_2566002 < baseStart_2566002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566006 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2566006 : Nat := 118140960795 + 2566006 * 2 ^ 59
def prefixEnd_2566006 : Nat := 4983230072969 + 3 ^ 40 * 2566006 * 2
def baseEnd_2566006 : Nat := 878396293547328482282773

theorem tailTrace_2566006 : CollatzResearch.WordTrace tailWord_2566006 prefixEnd_2566006 878396293547328482282773 := by
  unfold tailWord_2566006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849370471362873486245367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62393285027870650519950581 5849370471362873486245367)
  ·
    refine ⟨8774055707044310229368051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5849370471362873486245367 8774055707044310229368051)
    ·
      refine ⟨13161083560566465344052077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8774055707044310229368051 13161083560566465344052077)
      ·
        refine ⟨4935406335212424504019529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13161083560566465344052077 4935406335212424504019529)
        ·
          refine ⟨3701554751409318378014647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4935406335212424504019529 3701554751409318378014647)
          ·
            refine ⟨5552332127113977567021971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701554751409318378014647 5552332127113977567021971)
            ·
              refine ⟨8328498190670966350532957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552332127113977567021971 8328498190670966350532957)
              ·
                refine ⟨3123186821501612381449859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8328498190670966350532957 3123186821501612381449859)
                ·
                  refine ⟨4684780232252418572174789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123186821501612381449859 4684780232252418572174789)
                  ·
                    refine ⟨878396293547328482282773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4684780232252418572174789 878396293547328482282773)
                    ·
                      rfl

theorem cell22_2566006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2566006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566006 prefixEnd_2566006 := by exact prefixLift 2566006
  have htrace : WordTrace (prefixWord ++ tailWord_2566006) baseStart_2566006 baseEnd_2566006 := by
    simpa [prefixWord, tailWord_2566006, baseEnd_2566006] using wordTrace_append hprefix tailTrace_2566006
  have hstable : (prefixWord ++ tailWord_2566006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566006).length < 2 ^ (prefixWord ++ tailWord_2566006).sum := by decide
  have hdescent : baseEnd_2566006 < baseStart_2566006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566019 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 2, 3]
def baseStart_2566019 : Nat := 118140960795 + 2566019 * 2 ^ 59
def prefixEnd_2566019 : Nat := 4983230072969 + 3 ^ 40 * 2566019 * 2
def baseEnd_2566019 : Nat := 878400743713000781707733

theorem tailTrace_2566019 : CollatzResearch.WordTrace tailWord_2566019 prefixEnd_2566019 878400743713000781707733 := by
  unfold tailWord_2566019
  simp only [CollatzResearch.WordTrace]
  refine ⟨93590401690758879000149111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62393601127172586000099407 93590401690758879000149111)
  ·
    refine ⟨140385602536138318500223667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93590401690758879000149111 140385602536138318500223667)
    ·
      refine ⟨210578403804207477750335501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140385602536138318500223667 210578403804207477750335501)
      ·
        refine ⟨78966901426577804156375813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210578403804207477750335501 78966901426577804156375813)
        ·
          refine ⟨14806294017483338279320465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78966901426577804156375813 14806294017483338279320465)
          ·
            refine ⟨11104720513112503709490349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14806294017483338279320465 11104720513112503709490349)
            ·
              refine ⟨4164270192417188891058881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11104720513112503709490349 4164270192417188891058881)
              ·
                refine ⟨3123202644312891668294161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4164270192417188891058881 3123202644312891668294161)
                ·
                  refine ⟨2342401983234668751220621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3123202644312891668294161 2342401983234668751220621)
                  ·
                    refine ⟨878400743713000781707733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342401983234668751220621 878400743713000781707733)
                    ·
                      rfl

theorem cell22_2566019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 3].length) (baseStart_2566019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566019 prefixEnd_2566019 := by exact prefixLift 2566019
  have htrace : WordTrace (prefixWord ++ tailWord_2566019) baseStart_2566019 baseEnd_2566019 := by
    simpa [prefixWord, tailWord_2566019, baseEnd_2566019] using wordTrace_append hprefix tailTrace_2566019
  have hstable : (prefixWord ++ tailWord_2566019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566019).length < 2 ^ (prefixWord ++ tailWord_2566019).sum := by decide
  have hdescent : baseEnd_2566019 < baseStart_2566019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566077 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 7]
def baseStart_2566077 : Nat := 118140960795 + 2566077 * 2 ^ 59
def prefixEnd_2566077 : Nat := 4983230072969 + 3 ^ 40 * 2566077 * 2
def baseEnd_2566077 : Nat := 292806866099435987919185

theorem tailTrace_2566077 : CollatzResearch.WordTrace tailWord_2566077 prefixEnd_2566077 292806866099435987919185 := by
  unfold tailWord_2566077
  simp only [CollatzResearch.WordTrace]
  refine ⟨93592517124548754905760485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62395011416365836603840323 93592517124548754905760485)
  ·
    refine ⟨17548596960852891544830091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93592517124548754905760485 17548596960852891544830091)
    ·
      refine ⟨26322895441279337317245137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17548596960852891544830091 26322895441279337317245137)
      ·
        refine ⟨19742171580959502987933853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26322895441279337317245137 19742171580959502987933853)
        ·
          refine ⟨7403314342859813620475195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19742171580959502987933853 7403314342859813620475195)
          ·
            refine ⟨11104971514289720430712793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7403314342859813620475195 11104971514289720430712793)
            ·
              refine ⟨8328728635717290323034595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11104971514289720430712793 8328728635717290323034595)
              ·
                refine ⟨12493092953575935484551893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8328728635717290323034595 12493092953575935484551893)
                ·
                  refine ⟨292806866099435987919185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12493092953575935484551893 292806866099435987919185)
                  ·
                    rfl

theorem cell22_2566077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_2566077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566077 prefixEnd_2566077 := by exact prefixLift 2566077
  have htrace : WordTrace (prefixWord ++ tailWord_2566077) baseStart_2566077 baseEnd_2566077 := by
    simpa [prefixWord, tailWord_2566077, baseEnd_2566077] using wordTrace_append hprefix tailTrace_2566077
  have hstable : (prefixWord ++ tailWord_2566077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566077).length < 2 ^ (prefixWord ++ tailWord_2566077).sum := by decide
  have hdescent : baseEnd_2566077 < baseStart_2566077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566152 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_2566152 : Nat := 118140960795 + 2566152 * 2 ^ 59
def prefixEnd_2566152 : Nat := 4983230072969 + 3 ^ 40 * 2566152 * 2
def baseEnd_2566152 : Nat := 878446272331032768132325

theorem tailTrace_2566152 : CollatzResearch.WordTrace tailWord_2566152 prefixEnd_2566152 878446272331032768132325 := by
  unfold tailWord_2566152
  simp only [CollatzResearch.WordTrace]
  refine ⟨46797626299638521357370355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62396835066184695143160473 46797626299638521357370355)
  ·
    refine ⟨70196439449457782036055533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46797626299638521357370355 70196439449457782036055533)
    ·
      refine ⟨26323664793546668263520825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70196439449457782036055533 26323664793546668263520825)
      ·
        refine ⟨19742748595160001197640619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26323664793546668263520825 19742748595160001197640619)
        ·
          refine ⟨29614122892740001796460929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19742748595160001197640619 29614122892740001796460929)
          ·
            refine ⟨22210592169555001347345697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29614122892740001796460929 22210592169555001347345697)
            ·
              refine ⟨16657944127166251010509273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22210592169555001347345697 16657944127166251010509273)
              ·
                refine ⟨12493458095374688257881955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16657944127166251010509273 12493458095374688257881955)
                ·
                  refine ⟨18740187143062032386822933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12493458095374688257881955 18740187143062032386822933)
                  ·
                    refine ⟨878446272331032768132325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18740187143062032386822933 878446272331032768132325)
                    ·
                      rfl

theorem cell22_2566152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_2566152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566152 prefixEnd_2566152 := by exact prefixLift 2566152
  have htrace : WordTrace (prefixWord ++ tailWord_2566152) baseStart_2566152 baseEnd_2566152 := by
    simpa [prefixWord, tailWord_2566152, baseEnd_2566152] using wordTrace_append hprefix tailTrace_2566152
  have hstable : (prefixWord ++ tailWord_2566152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566152).length < 2 ^ (prefixWord ++ tailWord_2566152).sum := by decide
  have hdescent : baseEnd_2566152 < baseStart_2566152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566197 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2566197 : Nat := 118140960795 + 2566197 * 2 ^ 59
def prefixEnd_2566197 : Nat := 4983230072969 + 3 ^ 40 * 2566197 * 2
def baseEnd_2566197 : Nat := 878461676750667650757187

theorem tailTrace_2566197 : CollatzResearch.WordTrace tailWord_2566197 prefixEnd_2566197 878461676750667650757187 := by
  unfold tailWord_2566197
  simp only [CollatzResearch.WordTrace]
  refine ⟨93596893884114015400128845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62397929256076010266752563 93596893884114015400128845)
  ·
    refine ⟨35098835206542755775048317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93596893884114015400128845 35098835206542755775048317)
    ·
      refine ⟨13162063202453533415643119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35098835206542755775048317 13162063202453533415643119)
      ·
        refine ⟨19743094803680300123464679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13162063202453533415643119 19743094803680300123464679)
        ·
          refine ⟨29614642205520450185197019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19743094803680300123464679 29614642205520450185197019)
          ·
            refine ⟨44421963308280675277795529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29614642205520450185197019 44421963308280675277795529)
            ·
              refine ⟨33316472481210506458346647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44421963308280675277795529 33316472481210506458346647)
              ·
                refine ⟨49974708721815759687519971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33316472481210506458346647 49974708721815759687519971)
                ·
                  refine ⟨74962063082723639531279957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49974708721815759687519971 74962063082723639531279957)
                  ·
                    refine ⟨878461676750667650757187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74962063082723639531279957 878461676750667650757187)
                    ·
                      rfl

theorem cell22_2566197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2566197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566197 prefixEnd_2566197 := by exact prefixLift 2566197
  have htrace : WordTrace (prefixWord ++ tailWord_2566197) baseStart_2566197 baseEnd_2566197 := by
    simpa [prefixWord, tailWord_2566197, baseEnd_2566197] using wordTrace_append hprefix tailTrace_2566197
  have hstable : (prefixWord ++ tailWord_2566197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566197).length < 2 ^ (prefixWord ++ tailWord_2566197).sum := by decide
  have hdescent : baseEnd_2566197 < baseStart_2566197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566199 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 3, 3]
def baseStart_2566199 : Nat := 118140960795 + 2566199 * 2 ^ 59
def prefixEnd_2566199 : Nat := 4983230072969 + 3 ^ 40 * 2566199 * 2
def baseEnd_2566199 : Nat := 878462361391540312207181

theorem tailTrace_2566199 : CollatzResearch.WordTrace tailWord_2566199 prefixEnd_2566199 878462361391540312207181 := by
  unfold tailWord_2566199
  simp only [CollatzResearch.WordTrace]
  refine ⟨93596966830106769741701651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62397977886737846494467767 93596966830106769741701651)
  ·
    refine ⟨140395450245160154612552477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93596966830106769741701651 140395450245160154612552477)
    ·
      refine ⟨52648293841935057979707179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140395450245160154612552477 52648293841935057979707179)
      ·
        refine ⟨78972440762902586969560769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52648293841935057979707179 78972440762902586969560769)
        ·
          refine ⟨59229330572176940227170577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78972440762902586969560769 59229330572176940227170577)
          ·
            refine ⟨44421997929132705170377933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59229330572176940227170577 44421997929132705170377933)
            ·
              refine ⟨16658249223424764438891725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44421997929132705170377933 16658249223424764438891725)
              ·
                refine ⟨6246843458784286664584397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16658249223424764438891725 6246843458784286664584397)
                ·
                  refine ⟨2342566297044107499219149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6246843458784286664584397 2342566297044107499219149)
                  ·
                    refine ⟨878462361391540312207181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342566297044107499219149 878462361391540312207181)
                    ·
                      rfl

theorem cell22_2566199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_2566199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566199 prefixEnd_2566199 := by exact prefixLift 2566199
  have htrace : WordTrace (prefixWord ++ tailWord_2566199) baseStart_2566199 baseEnd_2566199 := by
    simpa [prefixWord, tailWord_2566199, baseEnd_2566199] using wordTrace_append hprefix tailTrace_2566199
  have hstable : (prefixWord ++ tailWord_2566199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566199).length < 2 ^ (prefixWord ++ tailWord_2566199).sum := by decide
  have hdescent : baseEnd_2566199 < baseStart_2566199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566250 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_2566250 : Nat := 118140960795 + 2566250 * 2 ^ 59
def prefixEnd_2566250 : Nat := 4983230072969 + 3 ^ 40 * 2566250 * 2
def baseEnd_2566250 : Nat := 878479819733793179182025

theorem tailTrace_2566250 : CollatzResearch.WordTrace tailWord_2566250 prefixEnd_2566250 878479819733793179182025 := by
  unfold tailWord_2566250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23399706738230501362952051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62399217968614670301205469 23399706738230501362952051)
  ·
    refine ⟨35099560107345752044428077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23399706738230501362952051 35099560107345752044428077)
    ·
      refine ⟨13162335040254657016660529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35099560107345752044428077 13162335040254657016660529)
      ·
        refine ⟨9871751280190992762495397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13162335040254657016660529 9871751280190992762495397)
        ·
          refine ⟨1850953365035811142967887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9871751280190992762495397 1850953365035811142967887)
          ·
            refine ⟨2776430047553716714451831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850953365035811142967887 2776430047553716714451831)
            ·
              refine ⟨4164645071330575071677747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776430047553716714451831 4164645071330575071677747)
              ·
                refine ⟨6246967606995862607516621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164645071330575071677747 6246967606995862607516621)
                ·
                  refine ⟨2342612852623448477818733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6246967606995862607516621 2342612852623448477818733)
                  ·
                    refine ⟨878479819733793179182025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342612852623448477818733 878479819733793179182025)
                    ·
                      rfl

theorem cell22_2566250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_2566250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566250 prefixEnd_2566250 := by exact prefixLift 2566250
  have htrace : WordTrace (prefixWord ++ tailWord_2566250) baseStart_2566250 baseEnd_2566250 := by
    simpa [prefixWord, tailWord_2566250, baseEnd_2566250] using wordTrace_append hprefix tailTrace_2566250
  have hstable : (prefixWord ++ tailWord_2566250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566250).length < 2 ^ (prefixWord ++ tailWord_2566250).sum := by decide
  have hdescent : baseEnd_2566250 < baseStart_2566250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566308 : List Nat := [2, 3, 1, 2, 4, 1, 1, 4, 4]
def baseStart_2566308 : Nat := 118140960795 + 2566308 * 2 ^ 59
def prefixEnd_2566308 : Nat := 4983230072969 + 3 ^ 40 * 2566308 * 2
def baseEnd_2566308 : Nat := 292833224773033453743949

theorem tailTrace_2566308 : CollatzResearch.WordTrace tailWord_2566308 prefixEnd_2566308 292833224773033453743949 := by
  unfold tailWord_2566308
  simp only [CollatzResearch.WordTrace]
  refine ⟨46800471193355940678709789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62400628257807920904946385 46800471193355940678709789)
  ·
    refine ⟨17550176697508477754516171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46800471193355940678709789 17550176697508477754516171)
    ·
      refine ⟨26325265046262716631774257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17550176697508477754516171 26325265046262716631774257)
      ·
        refine ⟨19743948784697037473830693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26325265046262716631774257 19743948784697037473830693)
        ·
          refine ⟨3701990397130694526343255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19743948784697037473830693 3701990397130694526343255)
          ·
            refine ⟨5552985595696041789514883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701990397130694526343255 5552985595696041789514883)
            ·
              refine ⟨8329478393544062684272325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552985595696041789514883 8329478393544062684272325)
              ·
                refine ⟨1561777198789511753301061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8329478393544062684272325 1561777198789511753301061)
                ·
                  refine ⟨292833224773033453743949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561777198789511753301061 292833224773033453743949)
                  ·
                    rfl

theorem cell22_2566308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_2566308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566308 prefixEnd_2566308 := by exact prefixLift 2566308
  have htrace : WordTrace (prefixWord ++ tailWord_2566308) baseStart_2566308 baseEnd_2566308 := by
    simpa [prefixWord, tailWord_2566308, baseEnd_2566308] using wordTrace_append hprefix tailTrace_2566308
  have hstable : (prefixWord ++ tailWord_2566308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566308).length < 2 ^ (prefixWord ++ tailWord_2566308).sum := by decide
  have hdescent : baseEnd_2566308 < baseStart_2566308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566336 : List Nat := [2, 1, 1, 2, 5, 2, 3, 6]
def baseStart_2566336 : Nat := 118140960795 + 2566336 * 2 ^ 59
def prefixEnd_2566336 : Nat := 4983230072969 + 3 ^ 40 * 2566336 * 2
def baseEnd_2566336 : Nat := 97612139921257513503529

theorem tailTrace_2566336 : CollatzResearch.WordTrace tailWord_2566336 prefixEnd_2566336 97612139921257513503529 := by
  unfold tailWord_2566336
  simp only [CollatzResearch.WordTrace]
  refine ⟨46800981815305221069719431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62401309087073628092959241 46800981815305221069719431)
  ·
    refine ⟨70201472722957831604579147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46800981815305221069719431 70201472722957831604579147)
    ·
      refine ⟨105302209084436747406868721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70201472722957831604579147 105302209084436747406868721)
      ·
        refine ⟨78976656813327560555151541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105302209084436747406868721 78976656813327560555151541)
        ·
          refine ⟨7404061576249458802045457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78976656813327560555151541 7404061576249458802045457)
          ·
            refine ⟨5553046182187094101534093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7404061576249458802045457 5553046182187094101534093)
            ·
              refine ⟨2082392318320160288075285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5553046182187094101534093 2082392318320160288075285)
              ·
                refine ⟨97612139921257513503529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2082392318320160288075285 97612139921257513503529)
                ·
                  rfl

theorem cell22_2566336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 6].length) (baseStart_2566336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566336 prefixEnd_2566336 := by exact prefixLift 2566336
  have htrace : WordTrace (prefixWord ++ tailWord_2566336) baseStart_2566336 baseEnd_2566336 := by
    simpa [prefixWord, tailWord_2566336, baseEnd_2566336] using wordTrace_append hprefix tailTrace_2566336
  have hstable : (prefixWord ++ tailWord_2566336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566336).length < 2 ^ (prefixWord ++ tailWord_2566336).sum := by decide
  have hdescent : baseEnd_2566336 < baseStart_2566336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566357 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2566357 : Nat := 118140960795 + 2566357 * 2 ^ 59
def prefixEnd_2566357 : Nat := 4983230072969 + 3 ^ 40 * 2566357 * 2
def baseEnd_2566357 : Nat := 878516448020480566756697

theorem tailTrace_2566357 : CollatzResearch.WordTrace tailWord_2566357 prefixEnd_2566357 878516448020480566756697 := by
  unfold tailWord_2566357
  simp only [CollatzResearch.WordTrace]
  refine ⟨93602729563534362725953325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62401819709022908483968883 93602729563534362725953325)
  ·
    refine ⟨35101023586325386022232497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93602729563534362725953325 35101023586325386022232497)
    ·
      refine ⟨26325767689744039516674373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35101023586325386022232497 26325767689744039516674373)
      ·
        refine ⟨4936081441827007409376445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26325767689744039516674373 4936081441827007409376445)
        ·
          refine ⟨1851030540685127778516167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4936081441827007409376445 1851030540685127778516167)
          ·
            refine ⟨2776545811027691667774251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851030540685127778516167 2776545811027691667774251)
            ·
              refine ⟨4164818716541537501661377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776545811027691667774251 4164818716541537501661377)
              ·
                refine ⟨3123614037406153126246033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4164818716541537501661377 3123614037406153126246033)
                ·
                  refine ⟨2342710528054614844684525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3123614037406153126246033 2342710528054614844684525)
                  ·
                    refine ⟨878516448020480566756697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342710528054614844684525 878516448020480566756697)
                    ·
                      rfl

theorem cell22_2566357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2566357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566357 prefixEnd_2566357 := by exact prefixLift 2566357
  have htrace : WordTrace (prefixWord ++ tailWord_2566357) baseStart_2566357 baseEnd_2566357 := by
    simpa [prefixWord, tailWord_2566357, baseEnd_2566357] using wordTrace_append hprefix tailTrace_2566357
  have hstable : (prefixWord ++ tailWord_2566357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566357).length < 2 ^ (prefixWord ++ tailWord_2566357).sum := by decide
  have hdescent : baseEnd_2566357 < baseStart_2566357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566368 : List Nat := [2, 1, 1, 3, 1, 3, 1, 6, 1, 3]
def baseStart_2566368 : Nat := 118140960795 + 2566368 * 2 ^ 59
def prefixEnd_2566368 : Nat := 4983230072969 + 3 ^ 40 * 2566368 * 2
def baseEnd_2566368 : Nat := 878520213545280204731663

theorem tailTrace_2566368 : CollatzResearch.WordTrace tailWord_2566368 prefixEnd_2566368 878520213545280204731663 := by
  unfold tailWord_2566368
  simp only [CollatzResearch.WordTrace]
  refine ⟨46801565383247255802301879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62402087177663007736402505 46801565383247255802301879)
  ·
    refine ⟨70202348074870883703452819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46801565383247255802301879 70202348074870883703452819)
    ·
      refine ⟨105303522112306325555179229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70202348074870883703452819 105303522112306325555179229)
      ·
        refine ⟨39488820792114872083192211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105303522112306325555179229 39488820792114872083192211)
        ·
          refine ⟨59233231188172308124788317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39488820792114872083192211 59233231188172308124788317)
          ·
            refine ⟨22212461695564615546795619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59233231188172308124788317 22212461695564615546795619)
            ·
              refine ⟨33318692543346923320193429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22212461695564615546795619 33318692543346923320193429)
              ·
                refine ⟨1561813712969387030634067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33318692543346923320193429 1561813712969387030634067)
                ·
                  refine ⟨2342720569454080545951101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561813712969387030634067 2342720569454080545951101)
                  ·
                    refine ⟨878520213545280204731663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342720569454080545951101 878520213545280204731663)
                    ·
                      rfl

theorem cell22_2566368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 3].length) (baseStart_2566368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566368 prefixEnd_2566368 := by exact prefixLift 2566368
  have htrace : WordTrace (prefixWord ++ tailWord_2566368) baseStart_2566368 baseEnd_2566368 := by
    simpa [prefixWord, tailWord_2566368, baseEnd_2566368] using wordTrace_append hprefix tailTrace_2566368
  have hstable : (prefixWord ++ tailWord_2566368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566368).length < 2 ^ (prefixWord ++ tailWord_2566368).sum := by decide
  have hdescent : baseEnd_2566368 < baseStart_2566368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566379 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 2, 5]
def baseStart_2566379 : Nat := 118140960795 + 2566379 * 2 ^ 59
def prefixEnd_2566379 : Nat := 4983230072969 + 3 ^ 40 * 2566379 * 2
def baseEnd_2566379 : Nat := 878523979070079842706629

theorem tailTrace_2566379 : CollatzResearch.WordTrace tailWord_2566379 prefixEnd_2566379 878523979070079842706629 := by
  unfold tailWord_2566379
  simp only [CollatzResearch.WordTrace]
  refine ⟨93603531969454660483254191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62402354646303106988836127 93603531969454660483254191)
  ·
    refine ⟨140405297954181990724881287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93603531969454660483254191 140405297954181990724881287)
    ·
      refine ⟨210607946931272986087321931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140405297954181990724881287 210607946931272986087321931)
      ·
        refine ⟨315911920396909479130982897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210607946931272986087321931 315911920396909479130982897)
        ·
          refine ⟨236933940297682109348237173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315911920396909479130982897 236933940297682109348237173)
          ·
            refine ⟨22212556902907697751397235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236933940297682109348237173 22212556902907697751397235)
            ·
              refine ⟨33318835354361546627095853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22212556902907697751397235 33318835354361546627095853)
              ·
                refine ⟨12494563257885579985160945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33318835354361546627095853 12494563257885579985160945)
                ·
                  refine ⟨9370922443414184988870709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12494563257885579985160945 9370922443414184988870709)
                  ·
                    refine ⟨878523979070079842706629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9370922443414184988870709 878523979070079842706629)
                    ·
                      rfl

theorem cell22_2566379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_2566379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566379 prefixEnd_2566379 := by exact prefixLift 2566379
  have htrace : WordTrace (prefixWord ++ tailWord_2566379) baseStart_2566379 baseEnd_2566379 := by
    simpa [prefixWord, tailWord_2566379, baseEnd_2566379] using wordTrace_append hprefix tailTrace_2566379
  have hstable : (prefixWord ++ tailWord_2566379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566379).length < 2 ^ (prefixWord ++ tailWord_2566379).sum := by decide
  have hdescent : baseEnd_2566379 < baseStart_2566379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566402 : List Nat := [3, 4, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2566402 : Nat := 118140960795 + 2566402 * 2 ^ 59
def prefixEnd_2566402 : Nat := 4983230072969 + 3 ^ 40 * 2566402 * 2
def baseEnd_2566402 : Nat := 878531852440115449381559

theorem tailTrace_2566402 : CollatzResearch.WordTrace tailWord_2566402 prefixEnd_2566402 878531852440115449381559 := by
  unfold tailWord_2566402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23401092712092833852835365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62402913898914223607560973 23401092712092833852835365)
  ·
    refine ⟨4387704883517406347406631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23401092712092833852835365 4387704883517406347406631)
    ·
      refine ⟨6581557325276109521109947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387704883517406347406631 6581557325276109521109947)
      ·
        refine ⟨9872335987914164281664921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6581557325276109521109947 9872335987914164281664921)
        ·
          refine ⟨7404251990935623211248691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9872335987914164281664921 7404251990935623211248691)
          ·
            refine ⟨11106377986403434816873037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7404251990935623211248691 11106377986403434816873037)
            ·
              refine ⟨4164891744901288056327389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11106377986403434816873037 4164891744901288056327389)
              ·
                refine ⟨1561834404337983021122771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4164891744901288056327389 1561834404337983021122771)
                ·
                  refine ⟨2342751606506974531684157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561834404337983021122771 2342751606506974531684157)
                  ·
                    refine ⟨878531852440115449381559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342751606506974531684157 878531852440115449381559)
                    ·
                      rfl

theorem cell22_2566402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2566402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566402 prefixEnd_2566402 := by exact prefixLift 2566402
  have htrace : WordTrace (prefixWord ++ tailWord_2566402) baseStart_2566402 baseEnd_2566402 := by
    simpa [prefixWord, tailWord_2566402, baseEnd_2566402] using wordTrace_append hprefix tailTrace_2566402
  have hstable : (prefixWord ++ tailWord_2566402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566402).length < 2 ^ (prefixWord ++ tailWord_2566402).sum := by decide
  have hdescent : baseEnd_2566402 < baseStart_2566402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566411 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 1, 4]
def baseStart_2566411 : Nat := 118140960795 + 2566411 * 2 ^ 59
def prefixEnd_2566411 : Nat := 4983230072969 + 3 ^ 40 * 2566411 * 2
def baseEnd_2566411 : Nat := 878534933324042425906531

theorem tailTrace_2566411 : CollatzResearch.WordTrace tailWord_2566411 prefixEnd_2566411 878534933324042425906531 := by
  unfold tailWord_2566411
  simp only [CollatzResearch.WordTrace]
  refine ⟨93604699105338729948419087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62403132736892486632279391 93604699105338729948419087)
  ·
    refine ⟨140407048658008094922628631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93604699105338729948419087 140407048658008094922628631)
    ·
      refine ⟨210610572987012142383942947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140407048658008094922628631 210610572987012142383942947)
      ·
        refine ⟨315915859480518213575914421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210610572987012142383942947 315915859480518213575914421)
        ·
          refine ⟨29617111826298582522741977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 315915859480518213575914421 29617111826298582522741977)
          ·
            refine ⟨22212833869723936892056483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29617111826298582522741977 22212833869723936892056483)
            ·
              refine ⟨33319250804585905338084725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22212833869723936892056483 33319250804585905338084725)
              ·
                refine ⟨3123679762929928625445443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33319250804585905338084725 3123679762929928625445443)
                ·
                  refine ⟨4685519644394892938168165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123679762929928625445443 4685519644394892938168165)
                  ·
                    refine ⟨878534933324042425906531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4685519644394892938168165 878534933324042425906531)
                    ·
                      rfl

theorem cell22_2566411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 4].length) (baseStart_2566411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566411 prefixEnd_2566411 := by exact prefixLift 2566411
  have htrace : WordTrace (prefixWord ++ tailWord_2566411) baseStart_2566411 baseEnd_2566411 := by
    simpa [prefixWord, tailWord_2566411, baseEnd_2566411] using wordTrace_append hprefix tailTrace_2566411
  have hstable : (prefixWord ++ tailWord_2566411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566411).length < 2 ^ (prefixWord ++ tailWord_2566411).sum := by decide
  have hdescent : baseEnd_2566411 < baseStart_2566411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566445 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2566445 : Nat := 118140960795 + 2566445 * 2 ^ 59
def prefixEnd_2566445 : Nat := 4983230072969 + 3 ^ 40 * 2566445 * 2
def baseEnd_2566445 : Nat := 878546572218877670556427

theorem tailTrace_2566445 : CollatzResearch.WordTrace tailWord_2566445 prefixEnd_2566445 878546572218877670556427 := by
  unfold tailWord_2566445
  simp only [CollatzResearch.WordTrace]
  refine ⟨93605939187215553755156789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62403959458143702503437859 93605939187215553755156789)
  ·
    refine ⟨8775556798801458164545949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93605939187215553755156789 8775556798801458164545949)
    ·
      refine ⟨3290833799550546811704731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8775556798801458164545949 3290833799550546811704731)
      ·
        refine ⟨4936250699325820217557097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3290833799550546811704731 4936250699325820217557097)
        ·
          refine ⟨3702188024494365163167823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4936250699325820217557097 3702188024494365163167823)
          ·
            refine ⟨5553282036741547744751735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702188024494365163167823 5553282036741547744751735)
            ·
              refine ⟨8329923055112321617127603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553282036741547744751735 8329923055112321617127603)
              ·
                refine ⟨12494884582668482425691405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8329923055112321617127603 12494884582668482425691405)
                ·
                  refine ⟨4685581718500680909634277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12494884582668482425691405 4685581718500680909634277)
                  ·
                    refine ⟨878546572218877670556427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4685581718500680909634277 878546572218877670556427)
                    ·
                      rfl

theorem cell22_2566445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2566445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566445 prefixEnd_2566445 := by exact prefixLift 2566445
  have htrace : WordTrace (prefixWord ++ tailWord_2566445) baseStart_2566445 baseEnd_2566445 := by
    simpa [prefixWord, tailWord_2566445, baseEnd_2566445] using wordTrace_append hprefix tailTrace_2566445
  have hstable : (prefixWord ++ tailWord_2566445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566445).length < 2 ^ (prefixWord ++ tailWord_2566445).sum := by decide
  have hdescent : baseEnd_2566445 < baseStart_2566445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566456 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_2566456 : Nat := 118140960795 + 2566456 * 2 ^ 59
def prefixEnd_2566456 : Nat := 4983230072969 + 3 ^ 40 * 2566456 * 2
def baseEnd_2566456 : Nat := 878550337743677308531393

theorem tailTrace_2566456 : CollatzResearch.WordTrace tailWord_2566456 prefixEnd_2566456 878550337743677308531393 := by
  unfold tailWord_2566456
  simp only [CollatzResearch.WordTrace]
  refine ⟨46803170195087851316903611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62404226926783801755871481 46803170195087851316903611)
  ·
    refine ⟨70204755292631776975355417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46803170195087851316903611 70204755292631776975355417)
    ·
      refine ⟨52653566469473832731516563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70204755292631776975355417 52653566469473832731516563)
      ·
        refine ⟨78980349704210749097274845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52653566469473832731516563 78980349704210749097274845)
        ·
          refine ⟨29617631139079030911478067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78980349704210749097274845 29617631139079030911478067)
          ·
            refine ⟨44426446708618546367217101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29617631139079030911478067 44426446708618546367217101)
            ·
              refine ⟨16659917515731954887706413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44426446708618546367217101 16659917515731954887706413)
              ·
                refine ⟨6247469068399483082889905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16659917515731954887706413 6247469068399483082889905)
                ·
                  refine ⟨4685601801299612312167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6247469068399483082889905 4685601801299612312167429)
                  ·
                    refine ⟨878550337743677308531393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4685601801299612312167429 878550337743677308531393)
                    ·
                      rfl

theorem cell22_2566456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_2566456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566456 prefixEnd_2566456 := by exact prefixLift 2566456
  have htrace : WordTrace (prefixWord ++ tailWord_2566456) baseStart_2566456 baseEnd_2566456 := by
    simpa [prefixWord, tailWord_2566456, baseEnd_2566456] using wordTrace_append hprefix tailTrace_2566456
  have hstable : (prefixWord ++ tailWord_2566456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566456).length < 2 ^ (prefixWord ++ tailWord_2566456).sum := by decide
  have hdescent : baseEnd_2566456 < baseStart_2566456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566494 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2566494 : Nat := 118140960795 + 2566494 * 2 ^ 59
def prefixEnd_2566494 : Nat := 4983230072969 + 3 ^ 40 * 2566494 * 2
def baseEnd_2566494 : Nat := 292854448640085958693759

theorem tailTrace_2566494 : CollatzResearch.WordTrace tailWord_2566494 prefixEnd_2566494 292854448640085958693759 := by
  unfold tailWord_2566494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11700965795504754390461317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62405150909358690082460357 11700965795504754390461317)
  ·
    refine ⟨2193931086657141448211497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11700965795504754390461317 2193931086657141448211497)
    ·
      refine ⟨1645448314992856086158623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2193931086657141448211497 1645448314992856086158623)
      ·
        refine ⟨2468172472489284129237935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645448314992856086158623 2468172472489284129237935)
        ·
          refine ⟨3702258708733926193856903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468172472489284129237935 3702258708733926193856903)
          ·
            refine ⟨5553388063100889290785355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702258708733926193856903 5553388063100889290785355)
            ·
              refine ⟨8330082094651333936178033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553388063100889290785355 8330082094651333936178033)
              ·
                refine ⟨6247561570988500452133525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8330082094651333936178033 6247561570988500452133525)
                ·
                  refine ⟨292854448640085958693759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6247561570988500452133525 292854448640085958693759)
                  ·
                    rfl

theorem cell22_2566494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2566494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566494 prefixEnd_2566494 := by exact prefixLift 2566494
  have htrace : WordTrace (prefixWord ++ tailWord_2566494) baseStart_2566494 baseEnd_2566494 := by
    simpa [prefixWord, tailWord_2566494, baseEnd_2566494] using wordTrace_append hprefix tailTrace_2566494
  have hstable : (prefixWord ++ tailWord_2566494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566494).length < 2 ^ (prefixWord ++ tailWord_2566494).sum := by decide
  have hdescent : baseEnd_2566494 < baseStart_2566494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566503 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2566503 : Nat := 118140960795 + 2566503 * 2 ^ 59
def prefixEnd_2566503 : Nat := 4983230072969 + 3 ^ 40 * 2566503 * 2
def baseEnd_2566503 : Nat := 878566426804184852606249

theorem tailTrace_2566503 : CollatzResearch.WordTrace tailWord_2566503 prefixEnd_2566503 878566426804184852606249 := by
  unfold tailWord_2566503
  simp only [CollatzResearch.WordTrace]
  refine ⟨93608054621005429660768163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62405369747336953107178775 93608054621005429660768163)
  ·
    refine ⟨140412081931508144491152245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93608054621005429660768163 140412081931508144491152245)
    ·
      refine ⟨13163632681078888546045523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140412081931508144491152245 13163632681078888546045523)
      ·
        refine ⟨19745449021618332819068285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13163632681078888546045523 19745449021618332819068285)
        ·
          refine ⟨7404543383106874807150607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19745449021618332819068285 7404543383106874807150607)
          ·
            refine ⟨11106815074660312210725911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7404543383106874807150607 11106815074660312210725911)
            ·
              refine ⟨16660222611990468316088867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11106815074660312210725911 16660222611990468316088867)
              ·
                refine ⟨24990333917985702474133301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16660222611990468316088867 24990333917985702474133301)
                ·
                  refine ⟨2342843804811159606949997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24990333917985702474133301 2342843804811159606949997)
                  ·
                    refine ⟨878566426804184852606249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342843804811159606949997 878566426804184852606249)
                    ·
                      rfl

theorem cell22_2566503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2566503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566503 prefixEnd_2566503 := by exact prefixLift 2566503
  have htrace : WordTrace (prefixWord ++ tailWord_2566503) baseStart_2566503 baseEnd_2566503 := by
    simpa [prefixWord, tailWord_2566503, baseEnd_2566503] using wordTrace_append hprefix tailTrace_2566503
  have hstable : (prefixWord ++ tailWord_2566503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566503).length < 2 ^ (prefixWord ++ tailWord_2566503).sum := by decide
  have hdescent : baseEnd_2566503 < baseStart_2566503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566563 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 1, 4]
def baseStart_2566563 : Nat := 118140960795 + 2566563 * 2 ^ 59
def prefixEnd_2566563 : Nat := 4983230072969 + 3 ^ 40 * 2566563 * 2
def baseEnd_2566563 : Nat := 878586966030364696106065

theorem tailTrace_2566563 : CollatzResearch.WordTrace tailWord_2566563 prefixEnd_2566563 878586966030364696106065 := by
  unfold tailWord_2566563
  simp only [CollatzResearch.WordTrace]
  refine ⟨93610243000788059907952343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62406828667192039938634895 93610243000788059907952343)
  ·
    refine ⟨140415364501182089861928515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93610243000788059907952343 140415364501182089861928515)
    ·
      refine ⟨210623046751773134792892773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140415364501182089861928515 210623046751773134792892773)
      ·
        refine ⟨39491821265957462773667395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210623046751773134792892773 39491821265957462773667395)
        ·
          refine ⟨59237731898936194160501093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39491821265957462773667395 59237731898936194160501093)
          ·
            refine ⟨11107074731050536405093955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59237731898936194160501093 11107074731050536405093955)
            ·
              refine ⟨16660612096575804607640933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11107074731050536405093955 16660612096575804607640933)
              ·
                refine ⟨3123864768107963363932675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16660612096575804607640933 3123864768107963363932675)
                ·
                  refine ⟨4685797152161945045899013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123864768107963363932675 4685797152161945045899013)
                  ·
                    refine ⟨878586966030364696106065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4685797152161945045899013 878586966030364696106065)
                    ·
                      rfl

theorem cell22_2566563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 4].length) (baseStart_2566563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566563 prefixEnd_2566563 := by exact prefixLift 2566563
  have htrace : WordTrace (prefixWord ++ tailWord_2566563) baseStart_2566563 baseEnd_2566563 := by
    simpa [prefixWord, tailWord_2566563, baseEnd_2566563] using wordTrace_append hprefix tailTrace_2566563
  have hstable : (prefixWord ++ tailWord_2566563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566563).length < 2 ^ (prefixWord ++ tailWord_2566563).sum := by decide
  have hdescent : baseEnd_2566563 < baseStart_2566563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566743 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 1, 6]
def baseStart_2566743 : Nat := 118140960795 + 2566743 * 2 ^ 59
def prefixEnd_2566743 : Nat := 4983230072969 + 3 ^ 40 * 2566743 * 2
def baseEnd_2566743 : Nat := 878648583708904226605513

theorem tailTrace_2566743 : CollatzResearch.WordTrace tailWord_2566743 prefixEnd_2566743 878648583708904226605513 := by
  unfold tailWord_2566743
  simp only [CollatzResearch.WordTrace]
  refine ⟨93616808140135950649504883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62411205426757300433003255 93616808140135950649504883)
  ·
    refine ⟨140425212210203925974257325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93616808140135950649504883 140425212210203925974257325)
    ·
      refine ⟨52659454578826472240346497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140425212210203925974257325 52659454578826472240346497)
      ·
        refine ⟨39494590934119854180259873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52659454578826472240346497 39494590934119854180259873)
        ·
          refine ⟨29620943200589890635194905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39494590934119854180259873 29620943200589890635194905)
          ·
            refine ⟨22215707400442417976396179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29620943200589890635194905 22215707400442417976396179)
            ·
              refine ⟨33323561100663626964594269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22215707400442417976396179 33323561100663626964594269)
              ·
                refine ⟨12496335412748860111722851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33323561100663626964594269 12496335412748860111722851)
                ·
                  refine ⟨18744503119123290167584277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12496335412748860111722851 18744503119123290167584277)
                  ·
                    refine ⟨878648583708904226605513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18744503119123290167584277 878648583708904226605513)
                    ·
                      rfl

theorem cell22_2566743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_2566743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566743 prefixEnd_2566743 := by exact prefixLift 2566743
  have htrace : WordTrace (prefixWord ++ tailWord_2566743) baseStart_2566743 baseEnd_2566743 := by
    simpa [prefixWord, tailWord_2566743, baseEnd_2566743] using wordTrace_append hprefix tailTrace_2566743
  have hstable : (prefixWord ++ tailWord_2566743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566743).length < 2 ^ (prefixWord ++ tailWord_2566743).sum := by decide
  have hdescent : baseEnd_2566743 < baseStart_2566743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566762 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_2566762 : Nat := 118140960795 + 2566762 * 2 ^ 59
def prefixEnd_2566762 : Nat := 4983230072969 + 3 ^ 40 * 2566762 * 2
def baseEnd_2566762 : Nat := 878655087797194510380455

theorem tailTrace_2566762 : CollatzResearch.WordTrace tailWord_2566762 prefixEnd_2566762 878655087797194510380455 := by
  unfold tailWord_2566762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23404375281766779223611635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62411667418044744596297693 23404375281766779223611635)
  ·
    refine ⟨35106562922650168835417453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23404375281766779223611635 35106562922650168835417453)
    ·
      refine ⟨13164961095993813313281545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35106562922650168835417453 13164961095993813313281545)
      ·
        refine ⟨9873720821995359984961159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13164961095993813313281545 9873720821995359984961159)
        ·
          refine ⟨14810581232993039977441739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9873720821995359984961159 14810581232993039977441739)
          ·
            refine ⟨22215871849489559966162609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14810581232993039977441739 22215871849489559966162609)
            ·
              refine ⟨16661903887117169974621957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22215871849489559966162609 16661903887117169974621957)
              ·
                refine ⟨3124106978834469370241617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16661903887117169974621957 3124106978834469370241617)
                ·
                  refine ⟨2343080234125852027681213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124106978834469370241617 2343080234125852027681213)
                  ·
                    refine ⟨878655087797194510380455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343080234125852027681213 878655087797194510380455)
                    ·
                      rfl

theorem cell22_2566762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_2566762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566762 prefixEnd_2566762 := by exact prefixLift 2566762
  have htrace : WordTrace (prefixWord ++ tailWord_2566762) baseStart_2566762 baseEnd_2566762 := by
    simpa [prefixWord, tailWord_2566762, baseEnd_2566762] using wordTrace_append hprefix tailTrace_2566762
  have hstable : (prefixWord ++ tailWord_2566762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566762).length < 2 ^ (prefixWord ++ tailWord_2566762).sum := by decide
  have hdescent : baseEnd_2566762 < baseStart_2566762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566826 : List Nat := [3, 1, 5, 2, 2, 1, 1, 7]
def baseStart_2566826 : Nat := 118140960795 + 2566826 * 2 ^ 59
def prefixEnd_2566826 : Nat := 4983230072969 + 3 ^ 40 * 2566826 * 2
def baseEnd_2566826 : Nat := 97630777367235519642251

theorem tailTrace_2566826 : CollatzResearch.WordTrace tailWord_2566826 prefixEnd_2566826 97630777367235519642251 := by
  unfold tailWord_2566826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23404958849708813956194083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62413223599223503883184221 23404958849708813956194083)
  ·
    refine ⟨35107438274563220934291125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23404958849708813956194083 35107438274563220934291125)
    ·
      refine ⟨3291322338240301962589793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35107438274563220934291125 3291322338240301962589793)
      ·
        refine ⟨2468491753680226471942345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3291322338240301962589793 2468491753680226471942345)
        ·
          refine ⟨1851368815260169853956759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2468491753680226471942345 1851368815260169853956759)
          ·
            refine ⟨2777053222890254780935139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851368815260169853956759 2777053222890254780935139)
            ·
              refine ⟨4165579834335382171402709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777053222890254780935139 4165579834335382171402709)
              ·
                refine ⟨97630777367235519642251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4165579834335382171402709 97630777367235519642251)
                ·
                  rfl

theorem cell22_2566826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_2566826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566826 prefixEnd_2566826 := by exact prefixLift 2566826
  have htrace : WordTrace (prefixWord ++ tailWord_2566826) baseStart_2566826 baseEnd_2566826 := by
    simpa [prefixWord, tailWord_2566826, baseEnd_2566826] using wordTrace_append hprefix tailTrace_2566826
  have hstable : (prefixWord ++ tailWord_2566826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566826).length < 2 ^ (prefixWord ++ tailWord_2566826).sum := by decide
  have hdescent : baseEnd_2566826 < baseStart_2566826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566835 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 2, 5]
def baseStart_2566835 : Nat := 118140960795 + 2566835 * 2 ^ 59
def prefixEnd_2566835 : Nat := 4983230072969 + 3 ^ 40 * 2566835 * 2
def baseEnd_2566835 : Nat := 878680077189046653305231

theorem tailTrace_2566835 : CollatzResearch.WordTrace tailWord_2566835 prefixEnd_2566835 878680077189046653305231 := by
  unfold tailWord_2566835
  simp only [CollatzResearch.WordTrace]
  refine ⟨93620163655802650361853959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62413442437201766907902639 93620163655802650361853959)
  ·
    refine ⟨140430245483703975542780939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93620163655802650361853959 140430245483703975542780939)
    ·
      refine ⟨210645368225555963314171409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140430245483703975542780939 210645368225555963314171409)
      ·
        refine ⟨157984026169166972485628557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210645368225555963314171409 157984026169166972485628557)
        ·
          refine ⟨59244009813437614682110709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157984026169166972485628557 59244009813437614682110709)
          ·
            refine ⟨5554125920009776376447879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59244009813437614682110709 5554125920009776376447879)
            ·
              refine ⟨8331188880014664564671819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554125920009776376447879 8331188880014664564671819)
              ·
                refine ⟨12496783320021996847007729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331188880014664564671819 12496783320021996847007729)
                ·
                  refine ⟨9372587490016497635255797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12496783320021996847007729 9372587490016497635255797)
                  ·
                    refine ⟨878680077189046653305231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9372587490016497635255797 878680077189046653305231)
                    ·
                      rfl

theorem cell22_2566835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_2566835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566835 prefixEnd_2566835 := by exact prefixLift 2566835
  have htrace : WordTrace (prefixWord ++ tailWord_2566835) baseStart_2566835 baseEnd_2566835 := by
    simpa [prefixWord, tailWord_2566835, baseEnd_2566835] using wordTrace_append hprefix tailTrace_2566835
  have hstable : (prefixWord ++ tailWord_2566835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566835).length < 2 ^ (prefixWord ++ tailWord_2566835).sum := by decide
  have hdescent : baseEnd_2566835 < baseStart_2566835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566837 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 5]
def baseStart_2566837 : Nat := 118140960795 + 2566837 * 2 ^ 59
def prefixEnd_2566837 : Nat := 4983230072969 + 3 ^ 40 * 2566837 * 2
def baseEnd_2566837 : Nat := 292893587276639771585075

theorem tailTrace_2566837 : CollatzResearch.WordTrace tailWord_2566837 prefixEnd_2566837 292893587276639771585075 := by
  unfold tailWord_2566837
  simp only [CollatzResearch.WordTrace]
  refine ⟨93620236601795404703426765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62413491067863603135617843 93620236601795404703426765)
  ·
    refine ⟨35107588725673276763785037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93620236601795404703426765 35107588725673276763785037)
    ·
      refine ⟨13165345772127478786419389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35107588725673276763785037 13165345772127478786419389)
      ·
        refine ⟨4937004664547804544907271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13165345772127478786419389 4937004664547804544907271)
        ·
          refine ⟨7405506996821706817360907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4937004664547804544907271 7405506996821706817360907)
          ·
            refine ⟨11108260495232560226041361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7405506996821706817360907 11108260495232560226041361)
            ·
              refine ⟨8331195371424420169531021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11108260495232560226041361 8331195371424420169531021)
              ·
                refine ⟨3124198264284157563574133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8331195371424420169531021 3124198264284157563574133)
                ·
                  refine ⟨292893587276639771585075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3124198264284157563574133 292893587276639771585075)
                  ·
                    rfl

theorem cell22_2566837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_2566837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566837 prefixEnd_2566837 := by exact prefixLift 2566837
  have htrace : WordTrace (prefixWord ++ tailWord_2566837) baseStart_2566837 baseEnd_2566837 := by
    simpa [prefixWord, tailWord_2566837, baseEnd_2566837] using wordTrace_append hprefix tailTrace_2566837
  have hstable : (prefixWord ++ tailWord_2566837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566837).length < 2 ^ (prefixWord ++ tailWord_2566837).sum := by decide
  have hdescent : baseEnd_2566837 < baseStart_2566837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566895 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 1, 6]
def baseStart_2566895 : Nat := 118140960795 + 2566895 * 2 ^ 59
def prefixEnd_2566895 : Nat := 4983230072969 + 3 ^ 40 * 2566895 * 2
def baseEnd_2566895 : Nat := 878700616415226496805047

theorem tailTrace_2566895 : CollatzResearch.WordTrace tailWord_2566895 prefixEnd_2566895 878700616415226496805047 := by
  unfold tailWord_2566895
  simp only [CollatzResearch.WordTrace]
  refine ⟨93622352035585280609038139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62414901357056853739358759 93622352035585280609038139)
  ·
    refine ⟨140433528053377920913557209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93622352035585280609038139 140433528053377920913557209)
    ·
      refine ⟨105325146040033440685167907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140433528053377920913557209 105325146040033440685167907)
      ·
        refine ⟨157987719060050161027751861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105325146040033440685167907 157987719060050161027751861)
        ·
          refine ⟨14811348661879702596351737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157987719060050161027751861 14811348661879702596351737)
          ·
            refine ⟨11108511496409776947263803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14811348661879702596351737 11108511496409776947263803)
            ·
              refine ⟨16662767244614665420895705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11108511496409776947263803 16662767244614665420895705)
              ·
                refine ⟨12497075433460999065671779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16662767244614665420895705 12497075433460999065671779)
                ·
                  refine ⟨18745613150191498598507669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12497075433460999065671779 18745613150191498598507669)
                  ·
                    refine ⟨878700616415226496805047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18745613150191498598507669 878700616415226496805047)
                    ·
                      rfl

theorem cell22_2566895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_2566895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566895 prefixEnd_2566895 := by exact prefixLift 2566895
  have htrace : WordTrace (prefixWord ++ tailWord_2566895) baseStart_2566895 baseEnd_2566895 := by
    simpa [prefixWord, tailWord_2566895, baseEnd_2566895] using wordTrace_append hprefix tailTrace_2566895
  have hstable : (prefixWord ++ tailWord_2566895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566895).length < 2 ^ (prefixWord ++ tailWord_2566895).sum := by decide
  have hdescent : baseEnd_2566895 < baseStart_2566895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566914 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2566914 : Nat := 118140960795 + 2566914 * 2 ^ 59
def prefixEnd_2566914 : Nat := 4983230072969 + 3 ^ 40 * 2566914 * 2
def baseEnd_2566914 : Nat := 878707120503516780579989

theorem tailTrace_2566914 : CollatzResearch.WordTrace tailWord_2566914 prefixEnd_2566914 878707120503516780579989 := by
  unfold tailWord_2566914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23405761255629111713494949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62415363348344297902653197 23405761255629111713494949)
  ·
    refine ⟨4388580235430458446280303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23405761255629111713494949 4388580235430458446280303)
    ·
      refine ⟨6582870353145687669420455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4388580235430458446280303 6582870353145687669420455)
      ·
        refine ⟨9874305529718531504130683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6582870353145687669420455 9874305529718531504130683)
        ·
          refine ⟨14811458294577797256196025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9874305529718531504130683 14811458294577797256196025)
          ·
            refine ⟨11108593720933347942147019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14811458294577797256196025 11108593720933347942147019)
            ·
              refine ⟨16662890581400021913220529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11108593720933347942147019 16662890581400021913220529)
              ·
                refine ⟨12497167936050016434915397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16662890581400021913220529 12497167936050016434915397)
                ·
                  refine ⟨2343218988009378081546637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12497167936050016434915397 2343218988009378081546637)
                  ·
                    refine ⟨878707120503516780579989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343218988009378081546637 878707120503516780579989)
                    ·
                      rfl

theorem cell22_2566914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2566914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566914 prefixEnd_2566914 := by exact prefixLift 2566914
  have htrace : WordTrace (prefixWord ++ tailWord_2566914) baseStart_2566914 baseEnd_2566914 := by
    simpa [prefixWord, tailWord_2566914, baseEnd_2566914] using wordTrace_append hprefix tailTrace_2566914
  have hstable : (prefixWord ++ tailWord_2566914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566914).length < 2 ^ (prefixWord ++ tailWord_2566914).sum := by decide
  have hdescent : baseEnd_2566914 < baseStart_2566914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566948 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_2566948 : Nat := 118140960795 + 2566948 * 2 ^ 59
def prefixEnd_2566948 : Nat := 4983230072969 + 3 ^ 40 * 2566948 * 2
def baseEnd_2566948 : Nat := 878718759398352025229885

theorem tailTrace_2566948 : CollatzResearch.WordTrace tailWord_2566948 prefixEnd_2566948 878718759398352025229885 := by
  unfold tailWord_2566948
  simp only [CollatzResearch.WordTrace]
  refine ⟨46812142552196635330358749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62416190069595513773811665 46812142552196635330358749)
  ·
    refine ⟨17554553457073738248884531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46812142552196635330358749 17554553457073738248884531)
    ·
      refine ⟨26331830185610607373326797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17554553457073738248884531 26331830185610607373326797)
      ·
        refine ⟨9874436319603977764997549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26331830185610607373326797 9874436319603977764997549)
        ·
          refine ⟨3702913619851491661874081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9874436319603977764997549 3702913619851491661874081)
          ·
            refine ⟨2777185214888618746405561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3702913619851491661874081 2777185214888618746405561)
            ·
              refine ⟨2082888911166464059804171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2777185214888618746405561 2082888911166464059804171)
              ·
                refine ⟨3124333366749696089706257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082888911166464059804171 3124333366749696089706257)
                ·
                  refine ⟨2343250025062272067279693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124333366749696089706257 2343250025062272067279693)
                  ·
                    refine ⟨878718759398352025229885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343250025062272067279693 878718759398352025229885)
                    ·
                      rfl

theorem cell22_2566948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_2566948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2566948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2566948 prefixEnd_2566948 := by exact prefixLift 2566948
  have htrace : WordTrace (prefixWord ++ tailWord_2566948) baseStart_2566948 baseEnd_2566948 := by
    simpa [prefixWord, tailWord_2566948, baseEnd_2566948] using wordTrace_append hprefix tailTrace_2566948
  have hstable : (prefixWord ++ tailWord_2566948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566948).length < 2 ^ (prefixWord ++ tailWord_2566948).sum := by decide
  have hdescent : baseEnd_2566948 < baseStart_2566948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567000 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 10]
def baseStart_2567000 : Nat := 118140960795 + 2567000 * 2 ^ 59
def prefixEnd_2567000 : Nat := 4983230072969 + 3 ^ 40 * 2567000 * 2
def baseEnd_2567000 : Nat := 292912186687013740976575

theorem tailTrace_2567000 : CollatzResearch.WordTrace tailWord_2567000 prefixEnd_2567000 292912186687013740976575 := by
  unfold tailWord_2567000
  simp only [CollatzResearch.WordTrace]
  refine ⟨46813090850102441770805227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62417454466803255694406969 46813090850102441770805227)
  ·
    refine ⟨70219636275153662656207841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46813090850102441770805227 70219636275153662656207841)
    ·
      refine ⟨52664727206365246992155881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70219636275153662656207841 52664727206365246992155881)
      ·
        refine ⟨39498545404773935244116911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52664727206365246992155881 39498545404773935244116911)
        ·
          refine ⟨59247818107160902866175367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39498545404773935244116911 59247818107160902866175367)
          ·
            refine ⟨88871727160741354299263051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59247818107160902866175367 88871727160741354299263051)
            ·
              refine ⟨133307590741112031448894577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88871727160741354299263051 133307590741112031448894577)
              ·
                refine ⟨99980693055834023586670933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133307590741112031448894577 99980693055834023586670933)
                ·
                  refine ⟨292912186687013740976575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 99980693055834023586670933 292912186687013740976575)
                  ·
                    rfl

theorem cell22_2567000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_2567000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567000 prefixEnd_2567000 := by exact prefixLift 2567000
  have htrace : WordTrace (prefixWord ++ tailWord_2567000) baseStart_2567000 baseEnd_2567000 := by
    simpa [prefixWord, tailWord_2567000, baseEnd_2567000] using wordTrace_append hprefix tailTrace_2567000
  have hstable : (prefixWord ++ tailWord_2567000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567000).length < 2 ^ (prefixWord ++ tailWord_2567000).sum := by decide
  have hdescent : baseEnd_2567000 < baseStart_2567000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567002 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_2567002 : Nat := 118140960795 + 2567002 * 2 ^ 59
def prefixEnd_2567002 : Nat := 4983230072969 + 3 ^ 40 * 2567002 * 2
def baseEnd_2567002 : Nat := 878737244701913884379719

theorem tailTrace_2567002 : CollatzResearch.WordTrace tailWord_2567002 prefixEnd_2567002 878737244701913884379719 := by
  unfold tailWord_2567002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23406563661549409470795815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62417503097465091922122173 23406563661549409470795815)
  ·
    refine ⟨35109845492324114206193723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23406563661549409470795815 35109845492324114206193723)
    ·
      refine ⟨52664768238486171309290585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35109845492324114206193723 52664768238486171309290585)
      ·
        refine ⟨39498576178864628481967939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52664768238486171309290585 39498576178864628481967939)
        ·
          refine ⟨59247864268296942722951909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39498576178864628481967939 59247864268296942722951909)
          ·
            refine ⟨11108974550305676760553483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59247864268296942722951909 11108974550305676760553483)
            ·
              refine ⟨16663461825458515140830225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11108974550305676760553483 16663461825458515140830225)
              ·
                refine ⟨12497596369093886355622669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16663461825458515140830225 12497596369093886355622669)
                ·
                  refine ⟨4686598638410207383358501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12497596369093886355622669 4686598638410207383358501)
                  ·
                    refine ⟨878737244701913884379719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4686598638410207383358501 878737244701913884379719)
                    ·
                      rfl

theorem cell22_2567002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_2567002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567002 prefixEnd_2567002 := by exact prefixLift 2567002
  have htrace : WordTrace (prefixWord ++ tailWord_2567002) baseStart_2567002 baseEnd_2567002 := by
    simpa [prefixWord, tailWord_2567002, baseEnd_2567002] using wordTrace_append hprefix tailTrace_2567002
  have hstable : (prefixWord ++ tailWord_2567002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567002).length < 2 ^ (prefixWord ++ tailWord_2567002).sum := by decide
  have hdescent : baseEnd_2567002 < baseStart_2567002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567004 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2567004 : Nat := 118140960795 + 2567004 * 2 ^ 59
def prefixEnd_2567004 : Nat := 4983230072969 + 3 ^ 40 * 2567004 * 2
def baseEnd_2567004 : Nat := 878737929342786545829713

theorem tailTrace_2567004 : CollatzResearch.WordTrace tailWord_2567004 prefixEnd_2567004 878737929342786545829713 := by
  unfold tailWord_2567004
  simp only [CollatzResearch.WordTrace]
  refine ⟨46813163796095196112378033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62417551728126928149837377 46813163796095196112378033)
  ·
    refine ⟨35109872847071397084283525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46813163796095196112378033 35109872847071397084283525)
    ·
      refine ⟨6583101158825886953303161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35109872847071397084283525 6583101158825886953303161)
      ·
        refine ⟨4937325869119415214977371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6583101158825886953303161 4937325869119415214977371)
        ·
          refine ⟨7405988803679122822466057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4937325869119415214977371 7405988803679122822466057)
          ·
            refine ⟨5554491602759342116849543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7405988803679122822466057 5554491602759342116849543)
            ·
              refine ⟨8331737404139013175274315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554491602759342116849543 8331737404139013175274315)
              ·
                refine ⟨12497606106208519762911473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331737404139013175274315 12497606106208519762911473)
                ·
                  refine ⟨9373204579656389822183605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12497606106208519762911473 9373204579656389822183605)
                  ·
                    refine ⟨878737929342786545829713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9373204579656389822183605 878737929342786545829713)
                    ·
                      rfl

theorem cell22_2567004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2567004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567004 prefixEnd_2567004 := by exact prefixLift 2567004
  have htrace : WordTrace (prefixWord ++ tailWord_2567004) baseStart_2567004 baseEnd_2567004 := by
    simpa [prefixWord, tailWord_2567004, baseEnd_2567004] using wordTrace_append hprefix tailTrace_2567004
  have hstable : (prefixWord ++ tailWord_2567004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567004).length < 2 ^ (prefixWord ++ tailWord_2567004).sum := by decide
  have hdescent : baseEnd_2567004 < baseStart_2567004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567049 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 4, 3]
def baseStart_2567049 : Nat := 118140960795 + 2567049 * 2 ^ 59
def prefixEnd_2567049 : Nat := 4983230072969 + 3 ^ 40 * 2567049 * 2
def baseEnd_2567049 : Nat := 878753333762421428454575

theorem tailTrace_2567049 : CollatzResearch.WordTrace tailWord_2567049 prefixEnd_2567049 878753333762421428454575 := by
  unfold tailWord_2567049
  simp only [CollatzResearch.WordTrace]
  refine ⟨93627968877027364910144201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62418645918018243273429467 93627968877027364910144201)
  ·
    refine ⟨70220976657770523682608151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93627968877027364910144201 70220976657770523682608151)
    ·
      refine ⟨105331464986655785523912227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70220976657770523682608151 105331464986655785523912227)
      ·
        refine ⟨157997197479983678285868341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105331464986655785523912227 157997197479983678285868341)
        ·
          refine ⟨14812237263748469839300157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157997197479983678285868341 14812237263748469839300157)
          ·
            refine ⟨5554588973905676189737559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14812237263748469839300157 5554588973905676189737559)
            ·
              refine ⟨8331883460858514284606339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554588973905676189737559 8331883460858514284606339)
              ·
                refine ⟨12497825191287771426909509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331883460858514284606339 12497825191287771426909509)
                ·
                  refine ⟨2343342223366457142545533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12497825191287771426909509 2343342223366457142545533)
                  ·
                    refine ⟨878753333762421428454575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343342223366457142545533 878753333762421428454575)
                    ·
                      rfl

theorem cell22_2567049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_2567049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567049 prefixEnd_2567049 := by exact prefixLift 2567049
  have htrace : WordTrace (prefixWord ++ tailWord_2567049) baseStart_2567049 baseEnd_2567049 := by
    simpa [prefixWord, tailWord_2567049, baseEnd_2567049] using wordTrace_append hprefix tailTrace_2567049
  have hstable : (prefixWord ++ tailWord_2567049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567049).length < 2 ^ (prefixWord ++ tailWord_2567049).sum := by decide
  have hdescent : baseEnd_2567049 < baseStart_2567049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567066 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_2567066 : Nat := 118140960795 + 2567066 * 2 ^ 59
def prefixEnd_2567066 : Nat := 4983230072969 + 3 ^ 40 * 2567066 * 2
def baseEnd_2567066 : Nat := 878759153209839050779523

theorem tailTrace_2567066 : CollatzResearch.WordTrace tailWord_2567066 prefixEnd_2567066 878759153209839050779523 := by
  unfold tailWord_2567066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23407147229491444203378263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62419059278643851209008701 23407147229491444203378263)
  ·
    refine ⟨35110720844237166305067395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23407147229491444203378263 35110720844237166305067395)
    ·
      refine ⟨52666081266355749457601093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35110720844237166305067395 52666081266355749457601093)
      ·
        refine ⟨9874890237441703023300205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52666081266355749457601093 9874890237441703023300205)
        ·
          refine ⟨3703083839040638633737577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9874890237441703023300205 3703083839040638633737577)
          ·
            refine ⟨2777312879280478975303183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3703083839040638633737577 2777312879280478975303183)
            ·
              refine ⟨4165969318920718462954775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777312879280478975303183 4165969318920718462954775)
              ·
                refine ⟨6248953978381077694432163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165969318920718462954775 6248953978381077694432163)
                ·
                  refine ⟨9373430967571616541648245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6248953978381077694432163 9373430967571616541648245)
                  ·
                    refine ⟨878759153209839050779523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9373430967571616541648245 878759153209839050779523)
                    ·
                      rfl

theorem cell22_2567066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_2567066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567066 prefixEnd_2567066 := by exact prefixLift 2567066
  have htrace : WordTrace (prefixWord ++ tailWord_2567066) baseStart_2567066 baseEnd_2567066 := by
    simpa [prefixWord, tailWord_2567066, baseEnd_2567066] using wordTrace_append hprefix tailTrace_2567066
  have hstable : (prefixWord ++ tailWord_2567066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567066).length < 2 ^ (prefixWord ++ tailWord_2567066).sum := by decide
  have hdescent : baseEnd_2567066 < baseStart_2567066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567079 : List Nat := [1, 1, 6, 1, 3, 1, 1, 8]
def baseStart_2567079 : Nat := 118140960795 + 2567079 * 2 ^ 59
def prefixEnd_2567079 : Nat := 4983230072969 + 3 ^ 40 * 2567079 * 2
def baseEnd_2567079 : Nat := 97640400375056816689387

theorem tailTrace_2567079 : CollatzResearch.WordTrace tailWord_2567079 prefixEnd_2567079 97640400375056816689387 := by
  unfold tailWord_2567079
  simp only [CollatzResearch.WordTrace]
  refine ⟨93629063066918680033736291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62419375377945786689157527 93629063066918680033736291)
  ·
    refine ⟨140443594600378020050604437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93629063066918680033736291 140443594600378020050604437)
    ·
      refine ⟨6583293496892719689872083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140443594600378020050604437 6583293496892719689872083)
      ·
        refine ⟨9874940245339079534808125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6583293496892719689872083 9874940245339079534808125)
        ·
          refine ⟨3703102592002154825553047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9874940245339079534808125 3703102592002154825553047)
          ·
            refine ⟨5554653888003232238329571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703102592002154825553047 5554653888003232238329571)
            ·
              refine ⟨8331980832004848357494357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554653888003232238329571 8331980832004848357494357)
              ·
                refine ⟨97640400375056816689387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8331980832004848357494357 97640400375056816689387)
                ·
                  rfl

theorem cell22_2567079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 8].length) (baseStart_2567079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567079 prefixEnd_2567079 := by exact prefixLift 2567079
  have htrace : WordTrace (prefixWord ++ tailWord_2567079) baseStart_2567079 baseEnd_2567079 := by
    simpa [prefixWord, tailWord_2567079, baseEnd_2567079] using wordTrace_append hprefix tailTrace_2567079
  have hstable : (prefixWord ++ tailWord_2567079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567079).length < 2 ^ (prefixWord ++ tailWord_2567079).sum := by decide
  have hdescent : baseEnd_2567079 < baseStart_2567079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567085 : List Nat := [1, 5, 2, 3, 1, 2, 1, 3, 4]
def baseStart_2567085 : Nat := 118140960795 + 2567085 * 2 ^ 59
def prefixEnd_2567085 : Nat := 4983230072969 + 3 ^ 40 * 2567085 * 2
def baseEnd_2567085 : Nat := 292921885766043111518155

theorem tailTrace_2567085 : CollatzResearch.WordTrace tailWord_2567085 prefixEnd_2567085 292921885766043111518155 := by
  unfold tailWord_2567085
  simp only [CollatzResearch.WordTrace]
  refine ⟨93629281904896943058454709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62419521269931295372303139 93629281904896943058454709)
  ·
    refine ⟨8777745178584088411730129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93629281904896943058454709 8777745178584088411730129)
    ·
      refine ⟨6583308883938066308797597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8777745178584088411730129 6583308883938066308797597)
      ·
        refine ⟨2468740831476774865799099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6583308883938066308797597 2468740831476774865799099)
        ·
          refine ⟨3703111247215162298698649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468740831476774865799099 3703111247215162298698649)
          ·
            refine ⟨2777333435411371724023987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3703111247215162298698649 2777333435411371724023987)
            ·
              refine ⟨4166000153117057586035981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777333435411371724023987 4166000153117057586035981)
              ·
                refine ⟨1562250057418896594763493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4166000153117057586035981 1562250057418896594763493)
                ·
                  refine ⟨292921885766043111518155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562250057418896594763493 292921885766043111518155)
                  ·
                    rfl

theorem cell22_2567085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_2567085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567085 prefixEnd_2567085 := by exact prefixLift 2567085
  have htrace : WordTrace (prefixWord ++ tailWord_2567085) baseStart_2567085 baseEnd_2567085 := by
    simpa [prefixWord, tailWord_2567085, baseEnd_2567085] using wordTrace_append hprefix tailTrace_2567085
  have hstable : (prefixWord ++ tailWord_2567085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567085).length < 2 ^ (prefixWord ++ tailWord_2567085).sum := by decide
  have hdescent : baseEnd_2567085 < baseStart_2567085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567111 : List Nat := [1, 1, 4, 1, 1, 2, 2, 6, 1, 3]
def baseStart_2567111 : Nat := 118140960795 + 2567111 * 2 ^ 59
def prefixEnd_2567111 : Nat := 4983230072969 + 3 ^ 40 * 2567111 * 2
def baseEnd_2567111 : Nat := 878774557629473933404385

theorem tailTrace_2567111 : CollatzResearch.WordTrace tailWord_2567111 prefixEnd_2567111 878774557629473933404385 := by
  unfold tailWord_2567111
  simp only [CollatzResearch.WordTrace]
  refine ⟨93630230202802749498901187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62420153468535166332600791 93630230202802749498901187)
  ·
    refine ⟨140445345304204124248351781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93630230202802749498901187 140445345304204124248351781)
    ·
      refine ⟨26333502244538273296565959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140445345304204124248351781 26333502244538273296565959)
      ·
        refine ⟨39500253366807409944848939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26333502244538273296565959 39500253366807409944848939)
        ·
          refine ⟨59250380050211114917273409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39500253366807409944848939 59250380050211114917273409)
          ·
            refine ⟨44437785037658336187955057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59250380050211114917273409 44437785037658336187955057)
            ·
              refine ⟨33328338778243752140966293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44437785037658336187955057 33328338778243752140966293)
              ·
                refine ⟨1562265880230175881607795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33328338778243752140966293 1562265880230175881607795)
                ·
                  refine ⟨2343398820345263822411693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562265880230175881607795 2343398820345263822411693)
                  ·
                    refine ⟨878774557629473933404385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343398820345263822411693 878774557629473933404385)
                    ·
                      rfl

theorem cell22_2567111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_2567111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567111 prefixEnd_2567111 := by exact prefixLift 2567111
  have htrace : WordTrace (prefixWord ++ tailWord_2567111) baseStart_2567111 baseEnd_2567111 := by
    simpa [prefixWord, tailWord_2567111, baseEnd_2567111] using wordTrace_append hprefix tailTrace_2567111
  have hstable : (prefixWord ++ tailWord_2567111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567111).length < 2 ^ (prefixWord ++ tailWord_2567111).sum := by decide
  have hdescent : baseEnd_2567111 < baseStart_2567111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567117 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2567117 : Nat := 118140960795 + 2567117 * 2 ^ 59
def prefixEnd_2567117 : Nat := 4983230072969 + 3 ^ 40 * 2567117 * 2
def baseEnd_2567117 : Nat := 878776611552091917754367

theorem tailTrace_2567117 : CollatzResearch.WordTrace tailWord_2567117 prefixEnd_2567117 878776611552091917754367 := by
  unfold tailWord_2567117
  simp only [CollatzResearch.WordTrace]
  refine ⟨93630449040781012523619605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62420299360520675015746403 93630449040781012523619605)
  ·
    refine ⟨4388927298786609962044669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93630449040781012523619605 4388927298786609962044669)
    ·
      refine ⟨1645847737044978735766751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4388927298786609962044669 1645847737044978735766751)
      ·
        refine ⟨2468771605567468103650127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645847737044978735766751 2468771605567468103650127)
        ·
          refine ⟨3703157408351202155475191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468771605567468103650127 3703157408351202155475191)
          ·
            refine ⟨5554736112526803233212787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703157408351202155475191 5554736112526803233212787)
            ·
              refine ⟨8332104168790204849819181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554736112526803233212787 8332104168790204849819181)
              ·
                refine ⟨3124539063296326818682193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8332104168790204849819181 3124539063296326818682193)
                ·
                  refine ⟨2343404297472245114011645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124539063296326818682193 2343404297472245114011645)
                  ·
                    refine ⟨878776611552091917754367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343404297472245114011645 878776611552091917754367)
                    ·
                      rfl

theorem cell22_2567117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2567117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567117 prefixEnd_2567117 := by exact prefixLift 2567117
  have htrace : WordTrace (prefixWord ++ tailWord_2567117) baseStart_2567117 baseEnd_2567117 := by
    simpa [prefixWord, tailWord_2567117, baseEnd_2567117] using wordTrace_append hprefix tailTrace_2567117
  have hstable : (prefixWord ++ tailWord_2567117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567117).length < 2 ^ (prefixWord ++ tailWord_2567117).sum := by decide
  have hdescent : baseEnd_2567117 < baseStart_2567117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567199 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 1, 6]
def baseStart_2567199 : Nat := 118140960795 + 2567199 * 2 ^ 59
def prefixEnd_2567199 : Nat := 4983230072969 + 3 ^ 40 * 2567199 * 2
def baseEnd_2567199 : Nat := 878804681827871037204115

theorem tailTrace_2567199 : CollatzResearch.WordTrace tailWord_2567199 prefixEnd_2567199 878804681827871037204115 := by
  unfold tailWord_2567199
  simp only [CollatzResearch.WordTrace]
  refine ⟨93633439826483940528104651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62422293217655960352069767 93633439826483940528104651)
  ·
    refine ⟨140450159739725910792156977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93633439826483940528104651 140450159739725910792156977)
    ·
      refine ⟨105337619804794433094117733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140450159739725910792156977 105337619804794433094117733)
      ·
        refine ⟨19750803713398956205147075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105337619804794433094117733 19750803713398956205147075)
        ·
          refine ⟨29626205570098434307720613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19750803713398956205147075 29626205570098434307720613)
          ·
            refine ⟨5554913544393456432697615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29626205570098434307720613 5554913544393456432697615)
            ·
              refine ⟨8332370316590184649046423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554913544393456432697615 8332370316590184649046423)
              ·
                refine ⟨12498555474885276973569635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8332370316590184649046423 12498555474885276973569635)
                ·
                  refine ⟨18747833212327915460354453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12498555474885276973569635 18747833212327915460354453)
                  ·
                    refine ⟨878804681827871037204115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18747833212327915460354453 878804681827871037204115)
                    ·
                      rfl

theorem cell22_2567199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_2567199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567199 prefixEnd_2567199 := by exact prefixLift 2567199
  have htrace : WordTrace (prefixWord ++ tailWord_2567199) baseStart_2567199 baseEnd_2567199 := by
    simpa [prefixWord, tailWord_2567199, baseEnd_2567199] using wordTrace_append hprefix tailTrace_2567199
  have hstable : (prefixWord ++ tailWord_2567199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567199).length < 2 ^ (prefixWord ++ tailWord_2567199).sum := by decide
  have hdescent : baseEnd_2567199 < baseStart_2567199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567214 : List Nat := [4, 1, 3, 1, 1, 1, 11]
def baseStart_2567214 : Nat := 118140960795 + 2567214 * 2 ^ 59
def prefixEnd_2567214 : Nat := 4983230072969 + 3 ^ 40 * 2567214 * 2
def baseEnd_2567214 : Nat := 32548511727200592521447

theorem tailTrace_2567214 : CollatzResearch.WordTrace tailWord_2567214 prefixEnd_2567214 32548511727200592521447 := by
  unfold tailWord_2567214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704248365178699761237587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62422657947619732059933797 11704248365178699761237587)
  ·
    refine ⟨17556372547768049641856381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11704248365178699761237587 17556372547768049641856381)
    ·
      refine ⟨6583639705413018615696143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17556372547768049641856381 6583639705413018615696143)
      ·
        refine ⟨9875459558119527923544215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6583639705413018615696143 9875459558119527923544215)
        ·
          refine ⟨14813189337179291885316323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9875459558119527923544215 14813189337179291885316323)
          ·
            refine ⟨22219784005768937827974485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14813189337179291885316323 22219784005768937827974485)
            ·
              refine ⟨32548511727200592521447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22219784005768937827974485 32548511727200592521447)
              ·
                rfl

theorem cell22_2567214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 11].length) (baseStart_2567214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567214 prefixEnd_2567214 := by exact prefixLift 2567214
  have htrace : WordTrace (prefixWord ++ tailWord_2567214) baseStart_2567214 baseEnd_2567214 := by
    simpa [prefixWord, tailWord_2567214, baseEnd_2567214] using wordTrace_append hprefix tailTrace_2567214
  have hstable : (prefixWord ++ tailWord_2567214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567214).length < 2 ^ (prefixWord ++ tailWord_2567214).sum := by decide
  have hdescent : baseEnd_2567214 < baseStart_2567214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567246 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_2567246 : Nat := 118140960795 + 2567246 * 2 ^ 59
def prefixEnd_2567246 : Nat := 4983230072969 + 3 ^ 40 * 2567246 * 2
def baseEnd_2567246 : Nat := 878820770888378581278971

theorem tailTrace_2567246 : CollatzResearch.WordTrace tailWord_2567246 prefixEnd_2567246 878820770888378581278971 := by
  unfold tailWord_2567246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704394257164208444383199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62423436038209111703377061 11704394257164208444383199)
  ·
    refine ⟨17556591385746312666574799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11704394257164208444383199 17556591385746312666574799)
    ·
      refine ⟨26334887078619468999862199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17556591385746312666574799 26334887078619468999862199)
      ·
        refine ⟨39502330617929203499793299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26334887078619468999862199 39502330617929203499793299)
        ·
          refine ⟨59253495926893805249689949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39502330617929203499793299 59253495926893805249689949)
          ·
            refine ⟨22220060972585176968633731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59253495926893805249689949 22220060972585176968633731)
            ·
              refine ⟨33330091458877765452950597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22220060972585176968633731 33330091458877765452950597)
              ·
                refine ⟨6249392148539581022428237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33330091458877765452950597 6249392148539581022428237)
                ·
                  refine ⟨2343522055702342883410589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6249392148539581022428237 2343522055702342883410589)
                  ·
                    refine ⟨878820770888378581278971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343522055702342883410589 878820770888378581278971)
                    ·
                      rfl

theorem cell22_2567246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_2567246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567246 prefixEnd_2567246 := by exact prefixLift 2567246
  have htrace : WordTrace (prefixWord ++ tailWord_2567246) baseStart_2567246 baseEnd_2567246 := by
    simpa [prefixWord, tailWord_2567246, baseEnd_2567246] using wordTrace_append hprefix tailTrace_2567246
  have hstable : (prefixWord ++ tailWord_2567246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567246).length < 2 ^ (prefixWord ++ tailWord_2567246).sum := by decide
  have hdescent : baseEnd_2567246 < baseStart_2567246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567254 : List Nat := [5, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2567254 : Nat := 118140960795 + 2567254 * 2 ^ 59
def prefixEnd_2567254 : Nat := 4983230072969 + 3 ^ 40 * 2567254 * 2
def baseEnd_2567254 : Nat := 292941169817289742359649

theorem tailTrace_2567254 : CollatzResearch.WordTrace tailWord_2567254 prefixEnd_2567254 292941169817289742359649 := by
  unfold tailWord_2567254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852215365080292807584801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62423630560856456614237877 5852215365080292807584801)
  ·
    refine ⟨4389161523810219605688601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5852215365080292807584801 4389161523810219605688601)
    ·
      refine ⟨3291871142857664704266451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4389161523810219605688601 3291871142857664704266451)
      ·
        refine ⟨4937806714286497056399677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3291871142857664704266451 4937806714286497056399677)
        ·
          refine ⟨1851677517857436396149879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4937806714286497056399677 1851677517857436396149879)
          ·
            refine ⟨2777516276786154594224819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851677517857436396149879 2777516276786154594224819)
            ·
              refine ⟨4166274415179231891337229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777516276786154594224819 4166274415179231891337229)
              ·
                refine ⟨1562352905692211959251461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4166274415179231891337229 1562352905692211959251461)
                ·
                  refine ⟨292941169817289742359649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562352905692211959251461 292941169817289742359649)
                  ·
                    rfl

theorem cell22_2567254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2567254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567254 prefixEnd_2567254 := by exact prefixLift 2567254
  have htrace : WordTrace (prefixWord ++ tailWord_2567254) baseStart_2567254 baseEnd_2567254 := by
    simpa [prefixWord, tailWord_2567254, baseEnd_2567254] using wordTrace_append hprefix tailTrace_2567254
  have hstable : (prefixWord ++ tailWord_2567254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567254).length < 2 ^ (prefixWord ++ tailWord_2567254).sum := by decide
  have hdescent : baseEnd_2567254 < baseStart_2567254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567280 : List Nat := [2, 1, 1, 1, 5, 1, 5, 2, 1, 3]
def baseStart_2567280 : Nat := 118140960795 + 2567280 * 2 ^ 59
def prefixEnd_2567280 : Nat := 4983230072969 + 3 ^ 40 * 2567280 * 2
def baseEnd_2567280 : Nat := 878832409783213825928867

theorem tailTrace_2567280 : CollatzResearch.WordTrace tailWord_2567280 prefixEnd_2567280 878832409783213825928867 := by
  unfold tailWord_2567280
  simp only [CollatzResearch.WordTrace]
  refine ⟨46818197069595245680901647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62424262759460327574535529 46818197069595245680901647)
  ·
    refine ⟨70227295604392868521352471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46818197069595245680901647 70227295604392868521352471)
    ·
      refine ⟨105340943406589302782028707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70227295604392868521352471 105340943406589302782028707)
      ·
        refine ⟨158011415109883954173043061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105340943406589302782028707 158011415109883954173043061)
        ·
          refine ⟨14813570166551620703722787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158011415109883954173043061 14813570166551620703722787)
          ·
            refine ⟨22220355249827431055584181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14813570166551620703722787 22220355249827431055584181)
            ·
              refine ⟨2083158304671321661461017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22220355249827431055584181 2083158304671321661461017)
              ·
                refine ⟨1562368728503491246095763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083158304671321661461017 1562368728503491246095763)
                ·
                  refine ⟨2343553092755236869143645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562368728503491246095763 2343553092755236869143645)
                  ·
                    refine ⟨878832409783213825928867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343553092755236869143645 878832409783213825928867)
                    ·
                      rfl

theorem cell22_2567280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 3].length) (baseStart_2567280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567280 prefixEnd_2567280 := by exact prefixLift 2567280
  have htrace : WordTrace (prefixWord ++ tailWord_2567280) baseStart_2567280 baseEnd_2567280 := by
    simpa [prefixWord, tailWord_2567280, baseEnd_2567280] using wordTrace_append hprefix tailTrace_2567280
  have hstable : (prefixWord ++ tailWord_2567280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567280).length < 2 ^ (prefixWord ++ tailWord_2567280).sum := by decide
  have hdescent : baseEnd_2567280 < baseStart_2567280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567306 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_2567306 : Nat := 118140960795 + 2567306 * 2 ^ 59
def prefixEnd_2567306 : Nat := 4983230072969 + 3 ^ 40 * 2567306 * 2
def baseEnd_2567306 : Nat := 878841310114558424778787

theorem tailTrace_2567306 : CollatzResearch.WordTrace tailWord_2567306 prefixEnd_2567306 878841310114558424778787 := by
  unfold tailWord_2567306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23409335609274074450562443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62424894958064198534833181 23409335609274074450562443)
  ·
    refine ⟨35114003413911111675843665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23409335609274074450562443 35114003413911111675843665)
    ·
      refine ⟨26335502560433333756882749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35114003413911111675843665 26335502560433333756882749)
      ·
        refine ⟨9875813460162500158831031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26335502560433333756882749 9875813460162500158831031)
        ·
          refine ⟨14813720190243750238246547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9875813460162500158831031 14813720190243750238246547)
          ·
            refine ⟨22220580285365625357369821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14813720190243750238246547 22220580285365625357369821)
            ·
              refine ⟨8332717607012109509013683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22220580285365625357369821 8332717607012109509013683)
              ·
                refine ⟨12499076410518164263520525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8332717607012109509013683 12499076410518164263520525)
                ·
                  refine ⟨4687153653944311598820197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12499076410518164263520525 4687153653944311598820197)
                  ·
                    refine ⟨878841310114558424778787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687153653944311598820197 878841310114558424778787)
                    ·
                      rfl

theorem cell22_2567306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_2567306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567306 prefixEnd_2567306 := by exact prefixLift 2567306
  have htrace : WordTrace (prefixWord ++ tailWord_2567306) baseStart_2567306 baseEnd_2567306 := by
    simpa [prefixWord, tailWord_2567306, baseEnd_2567306] using wordTrace_append hprefix tailTrace_2567306
  have hstable : (prefixWord ++ tailWord_2567306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567306).length < 2 ^ (prefixWord ++ tailWord_2567306).sum := by decide
  have hdescent : baseEnd_2567306 < baseStart_2567306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567353 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 2, 3]
def baseStart_2567353 : Nat := 118140960795 + 2567353 * 2 ^ 59
def prefixEnd_2567353 : Nat := 4983230072969 + 3 ^ 40 * 2567353 * 2
def baseEnd_2567353 : Nat := 878857399175065968853643

theorem tailTrace_2567353 : CollatzResearch.WordTrace tailWord_2567353 prefixEnd_2567353 878857399175065968853643 := by
  unfold tailWord_2567353
  simp only [CollatzResearch.WordTrace]
  refine ⟨93639056667926024829210713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62426037778617349886140475 93639056667926024829210713)
  ·
    refine ⟨70229292500944518621908035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93639056667926024829210713 70229292500944518621908035)
    ·
      refine ⟨105343938751416777932862053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70229292500944518621908035 105343938751416777932862053)
      ·
        refine ⟨19751988515890645862411635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105343938751416777932862053 19751988515890645862411635)
        ·
          refine ⟨29627982773835968793617453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19751988515890645862411635 29627982773835968793617453)
          ·
            refine ⟨11110493540188488297606545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29627982773835968793617453 11110493540188488297606545)
            ·
              refine ⟨8332870155141366223204909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11110493540188488297606545 8332870155141366223204909)
              ·
                refine ⟨3124826308178012333701841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8332870155141366223204909 3124826308178012333701841)
                ·
                  refine ⟨2343619731133509250276381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124826308178012333701841 2343619731133509250276381)
                  ·
                    refine ⟨878857399175065968853643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343619731133509250276381 878857399175065968853643)
                    ·
                      rfl

theorem cell22_2567353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_2567353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567353 prefixEnd_2567353 := by exact prefixLift 2567353
  have htrace : WordTrace (prefixWord ++ tailWord_2567353) baseStart_2567353 baseEnd_2567353 := by
    simpa [prefixWord, tailWord_2567353, baseEnd_2567353] using wordTrace_append hprefix tailTrace_2567353
  have hstable : (prefixWord ++ tailWord_2567353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567353).length < 2 ^ (prefixWord ++ tailWord_2567353).sum := by decide
  have hdescent : baseEnd_2567353 < baseStart_2567353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567379 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 4, 6]
def baseStart_2567379 : Nat := 118140960795 + 2567379 * 2 ^ 59
def prefixEnd_2567379 : Nat := 4983230072969 + 3 ^ 40 * 2567379 * 2
def baseEnd_2567379 : Nat := 878866299506410567703563

theorem tailTrace_2567379 : CollatzResearch.WordTrace tailWord_2567379 prefixEnd_2567379 878866299506410567703563 := by
  unfold tailWord_2567379
  simp only [CollatzResearch.WordTrace]
  refine ⟨93640004965831831269657191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62426669977221220846438127 93640004965831831269657191)
  ·
    refine ⟨140460007448747746904485787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93640004965831831269657191 140460007448747746904485787)
    ·
      refine ⟨210690011173121620356728681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140460007448747746904485787 210690011173121620356728681)
      ·
        refine ⟨158017508379841215267546511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210690011173121620356728681 158017508379841215267546511)
        ·
          refine ⟨237026262569761822901319767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158017508379841215267546511 237026262569761822901319767)
          ·
            refine ⟨355539393854642734351979651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237026262569761822901319767 355539393854642734351979651)
            ·
              refine ⟨533309090781964101527969477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355539393854642734351979651 533309090781964101527969477)
              ·
                refine ⟨99995454521618269036494277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533309090781964101527969477 99995454521618269036494277)
                ·
                  refine ⟨18749147722803425444342677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99995454521618269036494277 18749147722803425444342677)
                  ·
                    refine ⟨878866299506410567703563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18749147722803425444342677 878866299506410567703563)
                    ·
                      rfl

theorem cell22_2567379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_2567379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567379 prefixEnd_2567379 := by exact prefixLift 2567379
  have htrace : WordTrace (prefixWord ++ tailWord_2567379) baseStart_2567379 baseEnd_2567379 := by
    simpa [prefixWord, tailWord_2567379, baseEnd_2567379] using wordTrace_append hprefix tailTrace_2567379
  have hstable : (prefixWord ++ tailWord_2567379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567379).length < 2 ^ (prefixWord ++ tailWord_2567379).sum := by decide
  have hdescent : baseEnd_2567379 < baseStart_2567379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567471 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 1, 5]
def baseStart_2567471 : Nat := 118140960795 + 2567471 * 2 ^ 59
def prefixEnd_2567471 : Nat := 4983230072969 + 3 ^ 40 * 2567471 * 2
def baseEnd_2567471 : Nat := 878897792986552994403281

theorem tailTrace_2567471 : CollatzResearch.WordTrace tailWord_2567471 prefixEnd_2567471 878897792986552994403281 := by
  unfold tailWord_2567471
  simp only [CollatzResearch.WordTrace]
  refine ⟨93643360481498530982006267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62428906987665687321337511 93643360481498530982006267)
  ·
    refine ⟨140465040722247796473009401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93643360481498530982006267 140465040722247796473009401)
    ·
      refine ⟨105348780541685847354757051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140465040722247796473009401 105348780541685847354757051)
      ·
        refine ⟨158023170812528771032135577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105348780541685847354757051 158023170812528771032135577)
        ·
          refine ⟨118517378109396578274101683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158023170812528771032135577 118517378109396578274101683)
          ·
            refine ⟨177776067164094867411152525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118517378109396578274101683 177776067164094867411152525)
            ·
              refine ⟨66666025186535575279182197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177776067164094867411152525 66666025186535575279182197)
              ·
                refine ⟨6249939861237710182423331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66666025186535575279182197 6249939861237710182423331)
                ·
                  refine ⟨9374909791856565273634997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6249939861237710182423331 9374909791856565273634997)
                  ·
                    refine ⟨878897792986552994403281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9374909791856565273634997 878897792986552994403281)
                    ·
                      rfl

theorem cell22_2567471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_2567471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567471 prefixEnd_2567471 := by exact prefixLift 2567471
  have htrace : WordTrace (prefixWord ++ tailWord_2567471) baseStart_2567471 baseEnd_2567471 := by
    simpa [prefixWord, tailWord_2567471, baseEnd_2567471] using wordTrace_append hprefix tailTrace_2567471
  have hstable : (prefixWord ++ tailWord_2567471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567471).length < 2 ^ (prefixWord ++ tailWord_2567471).sum := by decide
  have hdescent : baseEnd_2567471 < baseStart_2567471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567475 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 1, 4]
def baseStart_2567475 : Nat := 118140960795 + 2567475 * 2 ^ 59
def prefixEnd_2567475 : Nat := 4983230072969 + 3 ^ 40 * 2567475 * 2
def baseEnd_2567475 : Nat := 878899162268298317303269

theorem tailTrace_2567475 : CollatzResearch.WordTrace tailWord_2567475 prefixEnd_2567475 878899162268298317303269 := by
  unfold tailWord_2567475
  simp only [CollatzResearch.WordTrace]
  refine ⟨93643506373484039665151879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62429004248989359776767919 93643506373484039665151879)
  ·
    refine ⟨140465259560226059497727819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93643506373484039665151879 140465259560226059497727819)
    ·
      refine ⟨210697889340339089246591729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140465259560226059497727819 210697889340339089246591729)
      ·
        refine ⟨158023417005254316934943797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210697889340339089246591729 158023417005254316934943797)
        ·
          refine ⟨14814695344242592212650981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158023417005254316934943797 14814695344242592212650981)
          ·
            refine ⟨2777755377045486039872059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14814695344242592212650981 2777755377045486039872059)
            ·
              refine ⟨4166633065568229059808089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777755377045486039872059 4166633065568229059808089)
              ·
                refine ⟨3124974799176171794856067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4166633065568229059808089 3124974799176171794856067)
                ·
                  refine ⟨4687462198764257692284101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124974799176171794856067 4687462198764257692284101)
                  ·
                    refine ⟨878899162268298317303269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687462198764257692284101 878899162268298317303269)
                    ·
                      rfl

theorem cell22_2567475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 4].length) (baseStart_2567475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567475 prefixEnd_2567475 := by exact prefixLift 2567475
  have htrace : WordTrace (prefixWord ++ tailWord_2567475) baseStart_2567475 baseEnd_2567475 := by
    simpa [prefixWord, tailWord_2567475, baseEnd_2567475] using wordTrace_append hprefix tailTrace_2567475
  have hstable : (prefixWord ++ tailWord_2567475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567475).length < 2 ^ (prefixWord ++ tailWord_2567475).sum := by decide
  have hdescent : baseEnd_2567475 < baseStart_2567475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567505 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 2, 3]
def baseStart_2567505 : Nat := 118140960795 + 2567505 * 2 ^ 59
def prefixEnd_2567505 : Nat := 4983230072969 + 3 ^ 40 * 2567505 * 2
def baseEnd_2567505 : Nat := 878909431881388239053177

theorem tailTrace_2567505 : CollatzResearch.WordTrace tailWord_2567505 prefixEnd_2567505 878909431881388239053177 := by
  unfold tailWord_2567505
  simp only [CollatzResearch.WordTrace]
  refine ⟨93644600563375354788743969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62429733708916903192495979 93644600563375354788743969)
  ·
    refine ⟨70233450422531516091557977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93644600563375354788743969 70233450422531516091557977)
    ·
      refine ⟨52675087816898637068668483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70233450422531516091557977 52675087816898637068668483)
      ·
        refine ⟨79012631725347955603002725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52675087816898637068668483 79012631725347955603002725)
        ·
          refine ⟨14814868448502741675563011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79012631725347955603002725 14814868448502741675563011)
          ·
            refine ⟨22222302672754112513344517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14814868448502741675563011 22222302672754112513344517)
            ·
              refine ⟨4166681751141396096252097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22222302672754112513344517 4166681751141396096252097)
              ·
                refine ⟨3125011313356047072189073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4166681751141396096252097 3125011313356047072189073)
                ·
                  refine ⟨2343758485017035304141805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3125011313356047072189073 2343758485017035304141805)
                  ·
                    refine ⟨878909431881388239053177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343758485017035304141805 878909431881388239053177)
                    ·
                      rfl

theorem cell22_2567505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_2567505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567505 prefixEnd_2567505 := by exact prefixLift 2567505
  have htrace : WordTrace (prefixWord ++ tailWord_2567505) baseStart_2567505 baseEnd_2567505 := by
    simpa [prefixWord, tailWord_2567505, baseEnd_2567505] using wordTrace_append hprefix tailTrace_2567505
  have hstable : (prefixWord ++ tailWord_2567505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567505).length < 2 ^ (prefixWord ++ tailWord_2567505).sum := by decide
  have hdescent : baseEnd_2567505 < baseStart_2567505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567546 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_2567546 : Nat := 118140960795 + 2567546 * 2 ^ 59
def prefixEnd_2567546 : Nat := 4983230072969 + 3 ^ 40 * 2567546 * 2
def baseEnd_2567546 : Nat := 292974489006425932926017

theorem tailTrace_2567546 : CollatzResearch.WordTrace tailWord_2567546 prefixEnd_2567546 292974489006425932926017 := by
  unfold tailWord_2567546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23411523989056704697746623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62430730637484545860657661 23411523989056704697746623)
  ·
    refine ⟨35117285983585057046619935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23411523989056704697746623 35117285983585057046619935)
    ·
      refine ⟨52675928975377585569929903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35117285983585057046619935 52675928975377585569929903)
      ·
        refine ⟨79013893463066378354894855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52675928975377585569929903 79013893463066378354894855)
        ·
          refine ⟨118520840194599567532342283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79013893463066378354894855 118520840194599567532342283)
          ·
            refine ⟨177781260291899351298513425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118520840194599567532342283 177781260291899351298513425)
            ·
              refine ⟨133335945218924513473885069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177781260291899351298513425 133335945218924513473885069)
              ·
                refine ⟨50000979457096692552706901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133335945218924513473885069 50000979457096692552706901)
                ·
                  refine ⟨292974489006425932926017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50000979457096692552706901 292974489006425932926017)
                  ·
                    rfl

theorem cell22_2567546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_2567546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567546 prefixEnd_2567546 := by exact prefixLift 2567546
  have htrace : WordTrace (prefixWord ++ tailWord_2567546) baseStart_2567546 baseEnd_2567546 := by
    simpa [prefixWord, tailWord_2567546, baseEnd_2567546] using wordTrace_append hprefix tailTrace_2567546
  have hstable : (prefixWord ++ tailWord_2567546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567546).length < 2 ^ (prefixWord ++ tailWord_2567546).sum := by decide
  have hdescent : baseEnd_2567546 < baseStart_2567546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567578 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_2567578 : Nat := 118140960795 + 2567578 * 2 ^ 59
def prefixEnd_2567578 : Nat := 4983230072969 + 3 ^ 40 * 2567578 * 2
def baseEnd_2567578 : Nat := 878934421273240381977953

theorem tailTrace_2567578 : CollatzResearch.WordTrace tailWord_2567578 prefixEnd_2567578 878934421273240381977953 := by
  unfold tailWord_2567578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23411815773027722064037847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62431508728073925504100925 23411815773027722064037847)
  ·
    refine ⟨35117723659541583096056771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23411815773027722064037847 35117723659541583096056771)
    ·
      refine ⟨52676585489312374644085157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35117723659541583096056771 52676585489312374644085157)
      ·
        refine ⟨9876859779246070245765967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52676585489312374644085157 9876859779246070245765967)
        ·
          refine ⟨14815289668869105368648951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9876859779246070245765967 14815289668869105368648951)
          ·
            refine ⟨22222934503303658052973427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14815289668869105368648951 22222934503303658052973427)
            ·
              refine ⟨33334401754955487079460141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22222934503303658052973427 33334401754955487079460141)
              ·
                refine ⟨12500400658108307654797553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33334401754955487079460141 12500400658108307654797553)
                ·
                  refine ⟨9375300493581230741098165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12500400658108307654797553 9375300493581230741098165)
                  ·
                    refine ⟨878934421273240381977953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9375300493581230741098165 878934421273240381977953)
                    ·
                      rfl

theorem cell22_2567578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_2567578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567578 prefixEnd_2567578 := by exact prefixLift 2567578
  have htrace : WordTrace (prefixWord ++ tailWord_2567578) baseStart_2567578 baseEnd_2567578 := by
    simpa [prefixWord, tailWord_2567578, baseEnd_2567578] using wordTrace_append hprefix tailTrace_2567578
  have hstable : (prefixWord ++ tailWord_2567578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567578).length < 2 ^ (prefixWord ++ tailWord_2567578).sum := by decide
  have hdescent : baseEnd_2567578 < baseStart_2567578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567655 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2567655 : Nat := 118140960795 + 2567655 * 2 ^ 59
def prefixEnd_2567655 : Nat := 4983230072969 + 3 ^ 40 * 2567655 * 2
def baseEnd_2567655 : Nat := 878960779946837847802717

theorem tailTrace_2567655 : CollatzResearch.WordTrace tailWord_2567655 prefixEnd_2567655 878960779946837847802717 := by
  unfold tailWord_2567655
  simp only [CollatzResearch.WordTrace]
  refine ⟨93650071512831930406704419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62433381008554620271136279 93650071512831930406704419)
  ·
    refine ⟨140475107269247895610056629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93650071512831930406704419 140475107269247895610056629)
    ·
      refine ⟨13169541306491990213442809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140475107269247895610056629 13169541306491990213442809)
      ·
        refine ⟨9877155979868992660082107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13169541306491990213442809 9877155979868992660082107)
        ·
          refine ⟨14815733969803488990123161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9877155979868992660082107 14815733969803488990123161)
          ·
            refine ⟨11111800477352616742592371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14815733969803488990123161 11111800477352616742592371)
            ·
              refine ⟨16667700716028925113888557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111800477352616742592371 16667700716028925113888557)
              ·
                refine ⟨6250387768510846917708209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16667700716028925113888557 6250387768510846917708209)
                ·
                  refine ⟨4687790826383135188281157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6250387768510846917708209 4687790826383135188281157)
                  ·
                    refine ⟨878960779946837847802717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687790826383135188281157 878960779946837847802717)
                    ·
                      rfl

theorem cell22_2567655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2567655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567655 prefixEnd_2567655 := by exact prefixLift 2567655
  have htrace : WordTrace (prefixWord ++ tailWord_2567655) baseStart_2567655 baseEnd_2567655 := by
    simpa [prefixWord, tailWord_2567655, baseEnd_2567655] using wordTrace_append hprefix tailTrace_2567655
  have hstable : (prefixWord ++ tailWord_2567655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567655).length < 2 ^ (prefixWord ++ tailWord_2567655).sum := by decide
  have hdescent : baseEnd_2567655 < baseStart_2567655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567685 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_2567685 : Nat := 118140960795 + 2567685 * 2 ^ 59
def prefixEnd_2567685 : Nat := 4983230072969 + 3 ^ 40 * 2567685 * 2
def baseEnd_2567685 : Nat := 878971049559927769552625

theorem tailTrace_2567685 : CollatzResearch.WordTrace tailWord_2567685 prefixEnd_2567685 878971049559927769552625 := by
  unfold tailWord_2567685
  simp only [CollatzResearch.WordTrace]
  refine ⟨93651165702723245530296509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62434110468482163686864339 93651165702723245530296509)
  ·
    refine ⟨35119187138521217073861191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93651165702723245530296509 35119187138521217073861191)
    ·
      refine ⟨52678780707781825610791787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35119187138521217073861191 52678780707781825610791787)
      ·
        refine ⟨79018171061672738416187681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52678780707781825610791787 79018171061672738416187681)
        ·
          refine ⟨59263628296254553812140761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79018171061672738416187681 59263628296254553812140761)
          ·
            refine ⟨44447721222190915359105571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59263628296254553812140761 44447721222190915359105571)
            ·
              refine ⟨66671581833286373038658357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44447721222190915359105571 66671581833286373038658357)
              ·
                refine ⟨6250460796870597472374221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66671581833286373038658357 6250460796870597472374221)
                ·
                  refine ⟨2343922798826474052140333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6250460796870597472374221 2343922798826474052140333)
                  ·
                    refine ⟨878971049559927769552625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2343922798826474052140333 878971049559927769552625)
                    ·
                      rfl

theorem cell22_2567685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_2567685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567685 prefixEnd_2567685 := by exact prefixLift 2567685
  have htrace : WordTrace (prefixWord ++ tailWord_2567685) baseStart_2567685 baseEnd_2567685 := by
    simpa [prefixWord, tailWord_2567685, baseEnd_2567685] using wordTrace_append hprefix tailTrace_2567685
  have hstable : (prefixWord ++ tailWord_2567685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567685).length < 2 ^ (prefixWord ++ tailWord_2567685).sum := by decide
  have hdescent : baseEnd_2567685 < baseStart_2567685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567762 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2567762 : Nat := 118140960795 + 2567762 * 2 ^ 59
def prefixEnd_2567762 : Nat := 4983230072969 + 3 ^ 40 * 2567762 * 2
def baseEnd_2567762 : Nat := 878997408233525235377389

theorem tailTrace_2567762 : CollatzResearch.WordTrace tailWord_2567762 prefixEnd_2567762 878997408233525235377389 := by
  unfold tailWord_2567762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23413493530861071920212385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62435982748962858453899693 23413493530861071920212385)
  ·
    refine ⟨17560120148145803940159289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23413493530861071920212385 17560120148145803940159289)
    ·
      refine ⟨13170090111109352955119467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17560120148145803940159289 13170090111109352955119467)
      ·
        refine ⟨19755135166664029432679201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13170090111109352955119467 19755135166664029432679201)
        ·
          refine ⟨14816351374998022074509401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19755135166664029432679201 14816351374998022074509401)
          ·
            refine ⟨11112263531248516555882051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14816351374998022074509401 11112263531248516555882051)
            ·
              refine ⟨16668395296872774833823077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11112263531248516555882051 16668395296872774833823077)
              ·
                refine ⟨3125324118163645281341827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16668395296872774833823077 3125324118163645281341827)
                ·
                  refine ⟨4687986177245467922012741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125324118163645281341827 4687986177245467922012741)
                  ·
                    refine ⟨878997408233525235377389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687986177245467922012741 878997408233525235377389)
                    ·
                      rfl

theorem cell22_2567762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2567762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567762 prefixEnd_2567762 := by exact prefixLift 2567762
  have htrace : WordTrace (prefixWord ++ tailWord_2567762) baseStart_2567762 baseEnd_2567762 := by
    simpa [prefixWord, tailWord_2567762, baseEnd_2567762] using wordTrace_append hprefix tailTrace_2567762
  have hstable : (prefixWord ++ tailWord_2567762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567762).length < 2 ^ (prefixWord ++ tailWord_2567762).sum := by decide
  have hdescent : baseEnd_2567762 < baseStart_2567762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567792 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 4, 3]
def baseStart_2567792 : Nat := 118140960795 + 2567792 * 2 ^ 59
def prefixEnd_2567792 : Nat := 4983230072969 + 3 ^ 40 * 2567792 * 2
def baseEnd_2567792 : Nat := 879007677846615157127297

theorem tailTrace_2567792 : CollatzResearch.WordTrace tailWord_2567792 prefixEnd_2567792 879007677846615157127297 := by
  unfold tailWord_2567792
  simp only [CollatzResearch.WordTrace]
  refine ⟨46827534156667801402220815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62436712208890401869627753 46827534156667801402220815)
  ·
    refine ⟨70241301235001702103331223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46827534156667801402220815 70241301235001702103331223)
    ·
      refine ⟨105361951852502553154996835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70241301235001702103331223 105361951852502553154996835)
      ·
        refine ⟨158042927778753829732495253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105361951852502553154996835 158042927778753829732495253)
        ·
          refine ⟨7408262239629085768710715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158042927778753829732495253 7408262239629085768710715)
          ·
            refine ⟨11112393359443628653066073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7408262239629085768710715 11112393359443628653066073)
            ·
              refine ⟨8334295019582721489799555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11112393359443628653066073 8334295019582721489799555)
              ·
                refine ⟨12501442529374082234699333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8334295019582721489799555 12501442529374082234699333)
                ·
                  refine ⟨2344020474257640419006125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12501442529374082234699333 2344020474257640419006125)
                  ·
                    refine ⟨879007677846615157127297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344020474257640419006125 879007677846615157127297)
                    ·
                      rfl

theorem cell22_2567792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_2567792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567792 prefixEnd_2567792 := by exact prefixLift 2567792
  have htrace : WordTrace (prefixWord ++ tailWord_2567792) baseStart_2567792 baseEnd_2567792 := by
    simpa [prefixWord, tailWord_2567792, baseEnd_2567792] using wordTrace_append hprefix tailTrace_2567792
  have hstable : (prefixWord ++ tailWord_2567792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567792).length < 2 ^ (prefixWord ++ tailWord_2567792).sum := by decide
  have hdescent : baseEnd_2567792 < baseStart_2567792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567805 : List Nat := [1, 4, 1, 1, 4, 1, 1, 9]
def baseStart_2567805 : Nat := 118140960795 + 2567805 * 2 ^ 59
def prefixEnd_2567805 : Nat := 4983230072969 + 3 ^ 40 * 2567805 * 2
def baseEnd_2567805 : Nat := 97668014223587495172473

theorem tailTrace_2567805 : CollatzResearch.WordTrace tailWord_2567805 prefixEnd_2567805 97668014223587495172473 := by
  unfold tailWord_2567805
  simp only [CollatzResearch.WordTrace]
  refine ⟨93655542462288506024664869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62437028308192337349776579 93655542462288506024664869)
  ·
    refine ⟨17560414211679094879624663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93655542462288506024664869 17560414211679094879624663)
    ·
      refine ⟨26340621317518642319436995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17560414211679094879624663 26340621317518642319436995)
      ·
        refine ⟨39510931976277963479155493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26340621317518642319436995 39510931976277963479155493)
        ·
          refine ⟨7408299745552118152341655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39510931976277963479155493 7408299745552118152341655)
          ·
            refine ⟨11112449618328177228512483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7408299745552118152341655 11112449618328177228512483)
            ·
              refine ⟨16668674427492265842768725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11112449618328177228512483 16668674427492265842768725)
              ·
                refine ⟨97668014223587495172473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16668674427492265842768725 97668014223587495172473)
                ·
                  rfl

theorem cell22_2567805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 9].length) (baseStart_2567805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567805 prefixEnd_2567805 := by exact prefixLift 2567805
  have htrace : WordTrace (prefixWord ++ tailWord_2567805) baseStart_2567805 baseEnd_2567805 := by
    simpa [prefixWord, tailWord_2567805, baseEnd_2567805] using wordTrace_append hprefix tailTrace_2567805
  have hstable : (prefixWord ++ tailWord_2567805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567805).length < 2 ^ (prefixWord ++ tailWord_2567805).sum := by decide
  have hdescent : baseEnd_2567805 < baseStart_2567805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567809 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2567809 : Nat := 118140960795 + 2567809 * 2 ^ 59
def prefixEnd_2567809 : Nat := 4983230072969 + 3 ^ 40 * 2567809 * 2
def baseEnd_2567809 : Nat := 879013497294032779452245

theorem tailTrace_2567809 : CollatzResearch.WordTrace tailWord_2567809 prefixEnd_2567809 879013497294032779452245 := by
  unfold tailWord_2567809
  simp only [CollatzResearch.WordTrace]
  refine ⟨93655688354274014707810481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62437125569516009805206987 93655688354274014707810481)
  ·
    refine ⟨70241766265705511030857861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93655688354274014707810481 70241766265705511030857861)
    ·
      refine ⟨13170331174819783318285849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70241766265705511030857861 13170331174819783318285849)
      ·
        refine ⟨9877748381114837488714387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13170331174819783318285849 9877748381114837488714387)
        ·
          refine ⟨14816622571672256233071581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9877748381114837488714387 14816622571672256233071581)
          ·
            refine ⟨5556233464377096087401843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14816622571672256233071581 5556233464377096087401843)
            ·
              refine ⟨8334350196565644131102765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5556233464377096087401843 8334350196565644131102765)
              ·
                refine ⟨3125381323712116549163537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8334350196565644131102765 3125381323712116549163537)
                ·
                  refine ⟨2344035992784087411872653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3125381323712116549163537 2344035992784087411872653)
                  ·
                    refine ⟨879013497294032779452245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344035992784087411872653 879013497294032779452245)
                    ·
                      rfl

theorem cell22_2567809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2567809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567809 prefixEnd_2567809 := by exact prefixLift 2567809
  have htrace : WordTrace (prefixWord ++ tailWord_2567809) baseStart_2567809 baseEnd_2567809 := by
    simpa [prefixWord, tailWord_2567809, baseEnd_2567809] using wordTrace_append hprefix tailTrace_2567809
  have hstable : (prefixWord ++ tailWord_2567809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567809).length < 2 ^ (prefixWord ++ tailWord_2567809).sum := by decide
  have hdescent : baseEnd_2567809 < baseStart_2567809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567865 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_2567865 : Nat := 118140960795 + 2567865 * 2 ^ 59
def prefixEnd_2567865 : Nat := 4983230072969 + 3 ^ 40 * 2567865 * 2
def baseEnd_2567865 : Nat := 879032667238467300052073

theorem tailTrace_2567865 : CollatzResearch.WordTrace tailWord_2567865 prefixEnd_2567865 879032667238467300052073 := by
  unfold tailWord_2567865
  simp only [CollatzResearch.WordTrace]
  refine ⟨93657730842071136271849049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62438487228047424181232699 93657730842071136271849049)
  ·
    refine ⟨70243298131553352203886787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93657730842071136271849049 70243298131553352203886787)
    ·
      refine ⟨105364947197330028305830181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70243298131553352203886787 105364947197330028305830181)
      ·
        refine ⟨19755927599499380307343159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105364947197330028305830181 19755927599499380307343159)
        ·
          refine ⟨29633891399249070461014739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19755927599499380307343159 29633891399249070461014739)
          ·
            refine ⟨44450837098873605691522109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29633891399249070461014739 44450837098873605691522109)
            ·
              refine ⟨16669063912077602134320791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44450837098873605691522109 16669063912077602134320791)
              ·
                refine ⟨25003595868116403201481187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16669063912077602134320791 25003595868116403201481187)
                ·
                  refine ⟨37505393802174604802221781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25003595868116403201481187 37505393802174604802221781)
                  ·
                    refine ⟨879032667238467300052073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37505393802174604802221781 879032667238467300052073)
                    ·
                      rfl

theorem cell22_2567865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_2567865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567865 prefixEnd_2567865 := by exact prefixLift 2567865
  have htrace : WordTrace (prefixWord ++ tailWord_2567865) baseStart_2567865 baseEnd_2567865 := by
    simpa [prefixWord, tailWord_2567865, baseEnd_2567865] using wordTrace_append hprefix tailTrace_2567865
  have hstable : (prefixWord ++ tailWord_2567865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567865).length < 2 ^ (prefixWord ++ tailWord_2567865).sum := by decide
  have hdescent : baseEnd_2567865 < baseStart_2567865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567895 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 8]
def baseStart_2567895 : Nat := 118140960795 + 2567895 * 2 ^ 59
def prefixEnd_2567895 : Nat := 4983230072969 + 3 ^ 40 * 2567895 * 2
def baseEnd_2567895 : Nat := 293014312283852407267327

theorem tailTrace_2567895 : CollatzResearch.WordTrace tailWord_2567895 prefixEnd_2567895 293014312283852407267327 := by
  unfold tailWord_2567895
  simp only [CollatzResearch.WordTrace]
  refine ⟨93658825031962451395441139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62439216687974967596960759 93658825031962451395441139)
  ·
    refine ⟨140488237547943677093161709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93658825031962451395441139 140488237547943677093161709)
    ·
      refine ⟨52683089080478878909935641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140488237547943677093161709 52683089080478878909935641)
      ·
        refine ⟨39512316810359159182451731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52683089080478878909935641 39512316810359159182451731)
        ·
          refine ⟨59268475215538738773677597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39512316810359159182451731 59268475215538738773677597)
          ·
            refine ⟨22225678205827027040129099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59268475215538738773677597 22225678205827027040129099)
            ·
              refine ⟨33338517308740540560193649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22225678205827027040129099 33338517308740540560193649)
              ·
                refine ⟨25003887981555405420145237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33338517308740540560193649 25003887981555405420145237)
                ·
                  refine ⟨293014312283852407267327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25003887981555405420145237 293014312283852407267327)
                  ·
                    rfl

theorem cell22_2567895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 8].length) (baseStart_2567895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567895 prefixEnd_2567895 := by exact prefixLift 2567895
  have htrace : WordTrace (prefixWord ++ tailWord_2567895) baseStart_2567895 baseEnd_2567895 := by
    simpa [prefixWord, tailWord_2567895, baseEnd_2567895] using wordTrace_append hprefix tailTrace_2567895
  have hstable : (prefixWord ++ tailWord_2567895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567895).length < 2 ^ (prefixWord ++ tailWord_2567895).sum := by decide
  have hdescent : baseEnd_2567895 < baseStart_2567895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567912 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 6]
def baseStart_2567912 : Nat := 118140960795 + 2567912 * 2 ^ 59
def prefixEnd_2567912 : Nat := 4983230072969 + 3 ^ 40 * 2567912 * 2
def baseEnd_2567912 : Nat := 293016252099658281375643

theorem tailTrace_2567912 : CollatzResearch.WordTrace tailWord_2567912 prefixEnd_2567912 293016252099658281375643 := by
  unfold tailWord_2567912
  simp only [CollatzResearch.WordTrace]
  refine ⟨46829722536450431649404995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62439630048600575532539993 46829722536450431649404995)
  ·
    refine ⟨70244583804675647474107493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46829722536450431649404995 70244583804675647474107493)
    ·
      refine ⟨13170859463376683901395155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70244583804675647474107493 13170859463376683901395155)
      ·
        refine ⟨19756289195065025852092733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13170859463376683901395155 19756289195065025852092733)
        ·
          refine ⟨7408608448149384694534775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19756289195065025852092733 7408608448149384694534775)
          ·
            refine ⟨11112912672224077041802163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7408608448149384694534775 11112912672224077041802163)
            ·
              refine ⟨16669369008336115562703245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11112912672224077041802163 16669369008336115562703245)
              ·
                refine ⟨6251013378126043336013717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16669369008336115562703245 6251013378126043336013717)
                ·
                  refine ⟨293016252099658281375643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6251013378126043336013717 293016252099658281375643)
                  ·
                    rfl

theorem cell22_2567912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_2567912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567912 prefixEnd_2567912 := by exact prefixLift 2567912
  have htrace : WordTrace (prefixWord ++ tailWord_2567912) baseStart_2567912 baseEnd_2567912 := by
    simpa [prefixWord, tailWord_2567912, baseEnd_2567912] using wordTrace_append hprefix tailTrace_2567912
  have hstable : (prefixWord ++ tailWord_2567912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567912).length < 2 ^ (prefixWord ++ tailWord_2567912).sum := by decide
  have hdescent : baseEnd_2567912 < baseStart_2567912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567927 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 1, 5]
def baseStart_2567927 : Nat := 118140960795 + 2567927 * 2 ^ 59
def prefixEnd_2567927 : Nat := 4983230072969 + 3 ^ 40 * 2567927 * 2
def baseEnd_2567927 : Nat := 879053891105519805001883

theorem tailTrace_2567927 : CollatzResearch.WordTrace tailWord_2567927 prefixEnd_2567927 879053891105519805001883 := by
  unfold tailWord_2567927
  simp only [CollatzResearch.WordTrace]
  refine ⟨93659992167846520860606035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62439994778564347240404023 93659992167846520860606035)
  ·
    refine ⟨140489988251769781290909053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93659992167846520860606035 140489988251769781290909053)
    ·
      refine ⟨52683745594413667984090895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140489988251769781290909053 52683745594413667984090895)
      ·
        refine ⟨79025618391620501976136343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52683745594413667984090895 79025618391620501976136343)
        ·
          refine ⟨118538427587430752964204515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79025618391620501976136343 118538427587430752964204515)
          ·
            refine ⟨177807641381146129446306773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118538427587430752964204515 177807641381146129446306773)
            ·
              refine ⟨4167366594870612408897815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 177807641381146129446306773 4167366594870612408897815)
              ·
                refine ⟨6251049892305918613346723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167366594870612408897815 6251049892305918613346723)
                ·
                  refine ⟨9376574838458877920020085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251049892305918613346723 9376574838458877920020085)
                  ·
                    refine ⟨879053891105519805001883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9376574838458877920020085 879053891105519805001883)
                    ·
                      rfl

theorem cell22_2567927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_2567927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567927 prefixEnd_2567927 := by exact prefixLift 2567927
  have htrace : WordTrace (prefixWord ++ tailWord_2567927) baseStart_2567927 baseEnd_2567927 := by
    simpa [prefixWord, tailWord_2567927, baseEnd_2567927] using wordTrace_append hprefix tailTrace_2567927
  have hstable : (prefixWord ++ tailWord_2567927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567927).length < 2 ^ (prefixWord ++ tailWord_2567927).sum := by decide
  have hdescent : baseEnd_2567927 < baseStart_2567927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567946 : List Nat := [3, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_2567946 : Nat := 118140960795 + 2567946 * 2 ^ 59
def prefixEnd_2567946 : Nat := 4983230072969 + 3 ^ 40 * 2567946 * 2
def baseEnd_2567946 : Nat := 293020131731270029592275

theorem tailTrace_2567946 : CollatzResearch.WordTrace tailWord_2567946 prefixEnd_2567946 293020131731270029592275 := by
  unfold tailWord_2567946
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415171288694421776386923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62440456769851791403698461 23415171288694421776386923)
  ·
    refine ⟨35122756933041632664580385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23415171288694421776386923 35122756933041632664580385)
    ·
      refine ⟨26342067699781224498435289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35122756933041632664580385 26342067699781224498435289)
      ·
        refine ⟨19756550774835918373826467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26342067699781224498435289 19756550774835918373826467)
        ·
          refine ⟨29634826162253877560739701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19756550774835918373826467 29634826162253877560739701)
          ·
            refine ⟨2778264952711301021319347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29634826162253877560739701 2778264952711301021319347)
            ·
              refine ⟨4167397429066951531979021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778264952711301021319347 4167397429066951531979021)
              ·
                refine ⟨1562774035900106824492133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4167397429066951531979021 1562774035900106824492133)
                ·
                  refine ⟨293020131731270029592275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562774035900106824492133 293020131731270029592275)
                  ·
                    rfl

theorem cell22_2567946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_2567946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567946 prefixEnd_2567946 := by exact prefixLift 2567946
  have htrace : WordTrace (prefixWord ++ tailWord_2567946) baseStart_2567946 baseEnd_2567946 := by
    simpa [prefixWord, tailWord_2567946, baseEnd_2567946] using wordTrace_append hprefix tailTrace_2567946
  have hstable : (prefixWord ++ tailWord_2567946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567946).length < 2 ^ (prefixWord ++ tailWord_2567946).sum := by decide
  have hdescent : baseEnd_2567946 < baseStart_2567946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567957 : List Nat := [1, 3, 2, 1, 2, 5, 8]
def baseStart_2567957 : Nat := 118140960795 + 2567957 * 2 ^ 59
def prefixEnd_2567957 : Nat := 4983230072969 + 3 ^ 40 * 2567957 * 2
def baseEnd_2567957 : Nat := 32557931878467026916733

theorem tailTrace_2567957 : CollatzResearch.WordTrace tailWord_2567957 prefixEnd_2567957 32557931878467026916733 := by
  unfold tailWord_2567957
  simp only [CollatzResearch.WordTrace]
  refine ⟨93661086357737835984198125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62440724238491890656132083 93661086357737835984198125)
  ·
    refine ⟨35122907384151688494074297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93661086357737835984198125 35122907384151688494074297)
    ·
      refine ⟨26342180538113766370555723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35122907384151688494074297 26342180538113766370555723)
      ·
        refine ⟨39513270807170649555833585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26342180538113766370555723 39513270807170649555833585)
        ·
          refine ⟨29634953105377987166875189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39513270807170649555833585 29634953105377987166875189)
          ·
            refine ⟨2778276853629186296894549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29634953105377987166875189 2778276853629186296894549)
            ·
              refine ⟨32557931878467026916733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2778276853629186296894549 32557931878467026916733)
              ·
                rfl

theorem cell22_2567957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 8].length) (baseStart_2567957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567957 prefixEnd_2567957 := by exact prefixLift 2567957
  have htrace : WordTrace (prefixWord ++ tailWord_2567957) baseStart_2567957 baseEnd_2567957 := by
    simpa [prefixWord, tailWord_2567957, baseEnd_2567957] using wordTrace_append hprefix tailTrace_2567957
  have hstable : (prefixWord ++ tailWord_2567957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567957).length < 2 ^ (prefixWord ++ tailWord_2567957).sum := by decide
  have hdescent : baseEnd_2567957 < baseStart_2567957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567959 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2567959 : Nat := 118140960795 + 2567959 * 2 ^ 59
def prefixEnd_2567959 : Nat := 4983230072969 + 3 ^ 40 * 2567959 * 2
def baseEnd_2567959 : Nat := 879064845359482388201785

theorem tailTrace_2567959 : CollatzResearch.WordTrace tailWord_2567959 prefixEnd_2567959 879064845359482388201785 := by
  unfold tailWord_2567959
  simp only [CollatzResearch.WordTrace]
  refine ⟨93661159303730590325770931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62440772869153726883847287 93661159303730590325770931)
  ·
    refine ⟨140491738955595885488656397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93661159303730590325770931 140491738955595885488656397)
    ·
      refine ⟨52684402108348457058246149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140491738955595885488656397 52684402108348457058246149)
      ·
        refine ⟨9878325395315335698421153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52684402108348457058246149 9878325395315335698421153)
        ·
          refine ⟨7408744046486501773815865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9878325395315335698421153 7408744046486501773815865)
          ·
            refine ⟨5556558034864876330361899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7408744046486501773815865 5556558034864876330361899)
            ·
              refine ⟨8334837052297314495542849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5556558034864876330361899 8334837052297314495542849)
              ·
                refine ⟨6251127789222985871657137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8334837052297314495542849 6251127789222985871657137)
                ·
                  refine ⟨4688345841917239403742853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6251127789222985871657137 4688345841917239403742853)
                  ·
                    refine ⟨879064845359482388201785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4688345841917239403742853 879064845359482388201785)
                    ·
                      rfl

theorem cell22_2567959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2567959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2567959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2567959 prefixEnd_2567959 := by exact prefixLift 2567959
  have htrace : WordTrace (prefixWord ++ tailWord_2567959) baseStart_2567959 baseEnd_2567959 := by
    simpa [prefixWord, tailWord_2567959, baseEnd_2567959] using wordTrace_append hprefix tailTrace_2567959
  have hstable : (prefixWord ++ tailWord_2567959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567959).length < 2 ^ (prefixWord ++ tailWord_2567959).sum := by decide
  have hdescent : baseEnd_2567959 < baseStart_2567959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568023 : List Nat := [1, 1, 3, 2, 5, 1, 1, 4, 1, 3]
def baseStart_2568023 : Nat := 118140960795 + 2568023 * 2 ^ 59
def prefixEnd_2568023 : Nat := 4983230072969 + 3 ^ 40 * 2568023 * 2
def baseEnd_2568023 : Nat := 879086753867407554601589

theorem tailTrace_2568023 : CollatzResearch.WordTrace tailWord_2568023 prefixEnd_2568023 879086753867407554601589 := by
  unfold tailWord_2568023
  simp only [CollatzResearch.WordTrace]
  refine ⟨93663493575498729256100723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62442329050332486170733815 93663493575498729256100723)
  ·
    refine ⟨140495240363248093884151085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93663493575498729256100723 140495240363248093884151085)
    ·
      refine ⟨52685715136218035206556657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140495240363248093884151085 52685715136218035206556657)
      ·
        refine ⟨39514286352163526404917493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52685715136218035206556657 39514286352163526404917493)
        ·
          refine ⟨3704464345515330600461015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39514286352163526404917493 3704464345515330600461015)
          ·
            refine ⟨5556696518272995900691523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704464345515330600461015 5556696518272995900691523)
            ·
              refine ⟨8335044777409493851037285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5556696518272995900691523 8335044777409493851037285)
              ·
                refine ⟨1562820895764280097069491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8335044777409493851037285 1562820895764280097069491)
                ·
                  refine ⟨2344231343646420145604237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562820895764280097069491 2344231343646420145604237)
                  ·
                    refine ⟨879086753867407554601589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344231343646420145604237 879086753867407554601589)
                    ·
                      rfl

theorem cell22_2568023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_2568023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568023 prefixEnd_2568023 := by exact prefixLift 2568023
  have htrace : WordTrace (prefixWord ++ tailWord_2568023) baseStart_2568023 baseEnd_2568023 := by
    simpa [prefixWord, tailWord_2568023, baseEnd_2568023] using wordTrace_append hprefix tailTrace_2568023
  have hstable : (prefixWord ++ tailWord_2568023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568023).length < 2 ^ (prefixWord ++ tailWord_2568023).sum := by decide
  have hdescent : baseEnd_2568023 < baseStart_2568023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568034 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2568034 : Nat := 118140960795 + 2568034 * 2 ^ 59
def prefixEnd_2568034 : Nat := 4983230072969 + 3 ^ 40 * 2568034 * 2
def baseEnd_2568034 : Nat := 879090519392207192576555

theorem tailTrace_2568034 : CollatzResearch.WordTrace tailWord_2568034 prefixEnd_2568034 879090519392207192576555 := by
  unfold tailWord_2568034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415973694614719533687789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62442596518972585423167437 23415973694614719533687789)
  ·
    refine ⟨8780990135480519825132921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23415973694614719533687789 8780990135480519825132921)
    ·
      refine ⟨6585742601610389868849691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8780990135480519825132921 6585742601610389868849691)
      ·
        refine ⟨9878613902415584803274537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6585742601610389868849691 9878613902415584803274537)
        ·
          refine ⟨7408960426811688602455903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9878613902415584803274537 7408960426811688602455903)
          ·
            refine ⟨11113440640217532903683855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7408960426811688602455903 11113440640217532903683855)
            ·
              refine ⟨16670160960326299355525783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11113440640217532903683855 16670160960326299355525783)
              ·
                refine ⟨25005241440489449033288675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16670160960326299355525783 25005241440489449033288675)
                ·
                  refine ⟨37507862160734173549933013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25005241440489449033288675 37507862160734173549933013)
                  ·
                    refine ⟨879090519392207192576555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37507862160734173549933013 879090519392207192576555)
                    ·
                      rfl

theorem cell22_2568034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2568034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568034 prefixEnd_2568034 := by exact prefixLift 2568034
  have htrace : WordTrace (prefixWord ++ tailWord_2568034) baseStart_2568034 baseEnd_2568034 := by
    simpa [prefixWord, tailWord_2568034, baseEnd_2568034] using wordTrace_append hprefix tailTrace_2568034
  have hstable : (prefixWord ++ tailWord_2568034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568034).length < 2 ^ (prefixWord ++ tailWord_2568034).sum := by decide
  have hdescent : baseEnd_2568034 < baseStart_2568034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568049 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_2568049 : Nat := 118140960795 + 2568049 * 2 ^ 59
def prefixEnd_2568049 : Nat := 4983230072969 + 3 ^ 40 * 2568049 * 2
def baseEnd_2568049 : Nat := 879095654198752153451509

theorem tailTrace_2568049 : CollatzResearch.WordTrace tailWord_2568049 prefixEnd_2568049 879095654198752153451509 := by
  unfold tailWord_2568049
  simp only [CollatzResearch.WordTrace]
  refine ⟨93664441873404535696547201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62442961248936357131031467 93664441873404535696547201)
  ·
    refine ⟨70248331405053401772410401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93664441873404535696547201 70248331405053401772410401)
    ·
      refine ⟨52686248553790051329307801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70248331405053401772410401 52686248553790051329307801)
      ·
        refine ⟨39514686415342538496980851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52686248553790051329307801 39514686415342538496980851)
        ·
          refine ⟨59272029623013807745471277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39514686415342538496980851 59272029623013807745471277)
          ·
            refine ⟨22227011108630177904551729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59272029623013807745471277 22227011108630177904551729)
            ·
              refine ⟨16670258331472633428413797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22227011108630177904551729 16670258331472633428413797)
              ·
                refine ⟨3125673437151118767827587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16670258331472633428413797 3125673437151118767827587)
                ·
                  refine ⟨4688510155726678151741381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125673437151118767827587 4688510155726678151741381)
                  ·
                    refine ⟨879095654198752153451509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4688510155726678151741381 879095654198752153451509)
                    ·
                      rfl

theorem cell22_2568049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_2568049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568049 prefixEnd_2568049 := by exact prefixLift 2568049
  have htrace : WordTrace (prefixWord ++ tailWord_2568049) baseStart_2568049 baseEnd_2568049 := by
    simpa [prefixWord, tailWord_2568049, baseEnd_2568049] using wordTrace_append hprefix tailTrace_2568049
  have hstable : (prefixWord ++ tailWord_2568049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568049).length < 2 ^ (prefixWord ++ tailWord_2568049).sum := by decide
  have hdescent : baseEnd_2568049 < baseStart_2568049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568248 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 4, 3]
def baseStart_2568248 : Nat := 118140960795 + 2568248 * 2 ^ 59
def prefixEnd_2568248 : Nat := 4983230072969 + 3 ^ 40 * 2568248 * 2
def baseEnd_2568248 : Nat := 879163775965581967725899

theorem tailTrace_2568248 : CollatzResearch.WordTrace tailWord_2568248 prefixEnd_2568248 879163775965581967725899 := by
  unfold tailWord_2568248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46835849999841796341520699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62447799999789061788694265 46835849999841796341520699)
  ·
    refine ⟨70253774999762694512281049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46835849999841796341520699 70253774999762694512281049)
    ·
      refine ⟨52690331249822020884210787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70253774999762694512281049 52690331249822020884210787)
      ·
        refine ⟨79035496874733031326316181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52690331249822020884210787 79035496874733031326316181)
        ·
          refine ⟨3704788916003110843421071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79035496874733031326316181 3704788916003110843421071)
          ·
            refine ⟨5557183374004666265131607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704788916003110843421071 5557183374004666265131607)
            ·
              refine ⟨8335775061006999397697411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557183374004666265131607 8335775061006999397697411)
              ·
                refine ⟨12503662591510499096546117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8335775061006999397697411 12503662591510499096546117)
                ·
                  refine ⟨2344436735908218580602397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12503662591510499096546117 2344436735908218580602397)
                  ·
                    refine ⟨879163775965581967725899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344436735908218580602397 879163775965581967725899)
                    ·
                      rfl

theorem cell22_2568248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_2568248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568248 prefixEnd_2568248 := by exact prefixLift 2568248
  have htrace : WordTrace (prefixWord ++ tailWord_2568248) baseStart_2568248 baseEnd_2568248 := by
    simpa [prefixWord, tailWord_2568248, baseEnd_2568248] using wordTrace_append hprefix tailTrace_2568248
  have hstable : (prefixWord ++ tailWord_2568248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568248).length < 2 ^ (prefixWord ++ tailWord_2568248).sum := by decide
  have hdescent : baseEnd_2568248 < baseStart_2568248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568306 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_2568306 : Nat := 118140960795 + 2568306 * 2 ^ 59
def prefixEnd_2568306 : Nat := 4983230072969 + 3 ^ 40 * 2568306 * 2
def baseEnd_2568306 : Nat := 293061210183629716591907

theorem tailTrace_2568306 : CollatzResearch.WordTrace tailWord_2568306 prefixEnd_2568306 293061210183629716591907 := by
  unfold tailWord_2568306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23418453858368367147163193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62449210288982312392435181 23418453858368367147163193)
  ·
    refine ⟨17563840393776275360372395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23418453858368367147163193 17563840393776275360372395)
    ·
      refine ⟨26345760590664413040558593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17563840393776275360372395 26345760590664413040558593)
      ·
        refine ⟨19759320442998309780418945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26345760590664413040558593 19759320442998309780418945)
        ·
          refine ⟨14819490332248732335314209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19759320442998309780418945 14819490332248732335314209)
          ·
            refine ⟨11114617749186549251485657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14819490332248732335314209 11114617749186549251485657)
            ·
              refine ⟨8335963311889911938614243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11114617749186549251485657 8335963311889911938614243)
              ·
                refine ⟨12503944967834867907921365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8335963311889911938614243 12503944967834867907921365)
                ·
                  refine ⟨293061210183629716591907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12503944967834867907921365 293061210183629716591907)
                  ·
                    rfl

theorem cell22_2568306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_2568306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568306 prefixEnd_2568306 := by exact prefixLift 2568306
  have htrace : WordTrace (prefixWord ++ tailWord_2568306) baseStart_2568306 baseEnd_2568306 := by
    simpa [prefixWord, tailWord_2568306, baseEnd_2568306] using wordTrace_append hprefix tailTrace_2568306
  have hstable : (prefixWord ++ tailWord_2568306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568306).length < 2 ^ (prefixWord ++ tailWord_2568306).sum := by decide
  have hdescent : baseEnd_2568306 < baseStart_2568306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568310 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_2568310 : Nat := 118140960795 + 2568310 * 2 ^ 59
def prefixEnd_2568310 : Nat := 4983230072969 + 3 ^ 40 * 2568310 * 2
def baseEnd_2568310 : Nat := 879184999832634472675709

theorem tailTrace_2568310 : CollatzResearch.WordTrace tailWord_2568310 prefixEnd_2568310 879184999832634472675709 := by
  unfold tailWord_2568310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854622582841186079487399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62449307550305984847865589 5854622582841186079487399)
  ·
    refine ⟨8781933874261779119231099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5854622582841186079487399 8781933874261779119231099)
    ·
      refine ⟨13172900811392668678846649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8781933874261779119231099 13172900811392668678846649)
      ·
        refine ⟨9879675608544501509134987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13172900811392668678846649 9879675608544501509134987)
        ·
          refine ⟨14819513412816752263702481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9879675608544501509134987 14819513412816752263702481)
          ·
            refine ⟨11114635059612564197776861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14819513412816752263702481 11114635059612564197776861)
            ·
              refine ⟨4167988147354711574166323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11114635059612564197776861 4167988147354711574166323)
              ·
                refine ⟨6251982221032067361249485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167988147354711574166323 6251982221032067361249485)
                ·
                  refine ⟨2344493332887025260468557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6251982221032067361249485 2344493332887025260468557)
                  ·
                    refine ⟨879184999832634472675709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344493332887025260468557 879184999832634472675709)
                    ·
                      rfl

theorem cell22_2568310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_2568310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568310 prefixEnd_2568310 := by exact prefixLift 2568310
  have htrace : WordTrace (prefixWord ++ tailWord_2568310) baseStart_2568310 baseEnd_2568310 := by
    simpa [prefixWord, tailWord_2568310, baseEnd_2568310] using wordTrace_append hprefix tailTrace_2568310
  have hstable : (prefixWord ++ tailWord_2568310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568310).length < 2 ^ (prefixWord ++ tailWord_2568310).sum := by decide
  have hdescent : baseEnd_2568310 < baseStart_2568310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568323 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 5]
def baseStart_2568323 : Nat := 118140960795 + 2568323 * 2 ^ 59
def prefixEnd_2568323 : Nat := 4983230072969 + 3 ^ 40 * 2568323 * 2
def baseEnd_2568323 : Nat := 293063149999435590700223

theorem tailTrace_2568323 : CollatzResearch.WordTrace tailWord_2568323 prefixEnd_2568323 293063149999435590700223 := by
  unfold tailWord_2568323
  simp only [CollatzResearch.WordTrace]
  refine ⟨93674435474411880492021623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62449623649607920328014415 93674435474411880492021623)
  ·
    refine ⟨140511653211617820738032435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93674435474411880492021623 140511653211617820738032435)
    ·
      refine ⟨210767479817426731107048653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140511653211617820738032435 210767479817426731107048653)
      ·
        refine ⟨79037804931535024165143245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210767479817426731107048653 79037804931535024165143245)
        ·
          refine ⟨29639176849325634061928717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79037804931535024165143245 29639176849325634061928717)
          ·
            refine ⟨11114691318497112773223269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29639176849325634061928717 11114691318497112773223269)
            ·
              refine ⟨2084004622218208644979363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11114691318497112773223269 2084004622218208644979363)
              ·
                refine ⟨3126006933327312967469045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084004622218208644979363 3126006933327312967469045)
                ·
                  refine ⟨293063149999435590700223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126006933327312967469045 293063149999435590700223)
                  ·
                    rfl

theorem cell22_2568323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 5].length) (baseStart_2568323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568323 prefixEnd_2568323 := by exact prefixLift 2568323
  have htrace : WordTrace (prefixWord ++ tailWord_2568323) baseStart_2568323 baseEnd_2568323 := by
    simpa [prefixWord, tailWord_2568323, baseEnd_2568323] using wordTrace_append hprefix tailTrace_2568323
  have hstable : (prefixWord ++ tailWord_2568323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568323).length < 2 ^ (prefixWord ++ tailWord_2568323).sum := by decide
  have hdescent : baseEnd_2568323 < baseStart_2568323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568336 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_2568336 : Nat := 118140960795 + 2568336 * 2 ^ 59
def prefixEnd_2568336 : Nat := 4983230072969 + 3 ^ 40 * 2568336 * 2
def baseEnd_2568336 : Nat := 879193900163979071525629

theorem tailTrace_2568336 : CollatzResearch.WordTrace tailWord_2568336 prefixEnd_2568336 879193900163979071525629 := by
  unfold tailWord_2568336
  simp only [CollatzResearch.WordTrace]
  refine ⟨46837454811682391856122431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62449939748909855808163241 46837454811682391856122431)
  ·
    refine ⟨70256182217523587784183647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46837454811682391856122431 70256182217523587784183647)
    ·
      refine ⟨105384273326285381676275471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70256182217523587784183647 105384273326285381676275471)
      ·
        refine ⟨158076409989428072514413207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105384273326285381676275471 158076409989428072514413207)
        ·
          refine ⟨237114614984142108771619811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158076409989428072514413207 237114614984142108771619811)
          ·
            refine ⟨355671922476213163157429717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237114614984142108771619811 355671922476213163157429717)
            ·
              refine ⟨8336060683036246011502259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 355671922476213163157429717 8336060683036246011502259)
              ·
                refine ⟨12504091024554369017253389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336060683036246011502259 12504091024554369017253389)
                ·
                  refine ⟨4689034134207888381470021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12504091024554369017253389 4689034134207888381470021)
                  ·
                    refine ⟨879193900163979071525629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689034134207888381470021 879193900163979071525629)
                    ·
                      rfl

theorem cell22_2568336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_2568336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568336 prefixEnd_2568336 := by exact prefixLift 2568336
  have htrace : WordTrace (prefixWord ++ tailWord_2568336) baseStart_2568336 baseEnd_2568336 := by
    simpa [prefixWord, tailWord_2568336, baseEnd_2568336] using wordTrace_append hprefix tailTrace_2568336
  have hstable : (prefixWord ++ tailWord_2568336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568336).length < 2 ^ (prefixWord ++ tailWord_2568336).sum := by decide
  have hdescent : baseEnd_2568336 < baseStart_2568336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568381 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2568381 : Nat := 118140960795 + 2568381 * 2 ^ 59
def prefixEnd_2568381 : Nat := 4983230072969 + 3 ^ 40 * 2568381 * 2
def baseEnd_2568381 : Nat := 879209304583613954150491

theorem tailTrace_2568381 : CollatzResearch.WordTrace tailWord_2568381 prefixEnd_2568381 879209304583613954150491 := by
  unfold tailWord_2568381
  simp only [CollatzResearch.WordTrace]
  refine ⟨93676550908201756397632997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62451033938801170931755331 93676550908201756397632997)
  ·
    refine ⟨17564353295287829324556187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93676550908201756397632997 17564353295287829324556187)
    ·
      refine ⟨26346529942931743986834281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17564353295287829324556187 26346529942931743986834281)
      ·
        refine ⟨19759897457198807990125711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26346529942931743986834281 19759897457198807990125711)
        ·
          refine ⟨29639846185798211985188567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19759897457198807990125711 29639846185798211985188567)
          ·
            refine ⟨44459769278697317977782851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29639846185798211985188567 44459769278697317977782851)
            ·
              refine ⟨66689653918045976966674277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44459769278697317977782851 66689653918045976966674277)
              ·
                refine ⟨12504310109633620681251427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66689653918045976966674277 12504310109633620681251427)
                ·
                  refine ⟨18756465164450431021877141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12504310109633620681251427 18756465164450431021877141)
                  ·
                    refine ⟨879209304583613954150491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18756465164450431021877141 879209304583613954150491)
                    ·
                      rfl

theorem cell22_2568381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2568381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568381 prefixEnd_2568381 := by exact prefixLift 2568381
  have htrace : WordTrace (prefixWord ++ tailWord_2568381) baseStart_2568381 baseEnd_2568381 := by
    simpa [prefixWord, tailWord_2568381, baseEnd_2568381] using wordTrace_append hprefix tailTrace_2568381
  have hstable : (prefixWord ++ tailWord_2568381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568381).length < 2 ^ (prefixWord ++ tailWord_2568381).sum := by decide
  have hdescent : baseEnd_2568381 < baseStart_2568381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568385 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 6]
def baseStart_2568385 : Nat := 118140960795 + 2568385 * 2 ^ 59
def prefixEnd_2568385 : Nat := 4983230072969 + 3 ^ 40 * 2568385 * 2
def baseEnd_2568385 : Nat := 293070224621786425683493

theorem tailTrace_2568385 : CollatzResearch.WordTrace tailWord_2568385 prefixEnd_2568385 293070224621786425683493 := by
  unfold tailWord_2568385
  simp only [CollatzResearch.WordTrace]
  refine ⟨93676696800187265080778609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62451131200124843387185739 93676696800187265080778609)
  ·
    refine ⟨70257522600140448810583957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93676696800187265080778609 70257522600140448810583957)
    ·
      refine ⟨3293321371881583537996123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70257522600140448810583957 3293321371881583537996123)
      ·
        refine ⟨4939982057822375306994185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293321371881583537996123 4939982057822375306994185)
        ·
          refine ⟨3704986543366781480245639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4939982057822375306994185 3704986543366781480245639)
          ·
            refine ⟨5557479815050172220368459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704986543366781480245639 5557479815050172220368459)
            ·
              refine ⟨8336219722575258330552689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557479815050172220368459 8336219722575258330552689)
              ·
                refine ⟨6252164791931443747914517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8336219722575258330552689 6252164791931443747914517)
                ·
                  refine ⟨293070224621786425683493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6252164791931443747914517 293070224621786425683493)
                  ·
                    rfl

theorem cell22_2568385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_2568385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568385 prefixEnd_2568385 := by exact prefixLift 2568385
  have htrace : WordTrace (prefixWord ++ tailWord_2568385) baseStart_2568385 baseEnd_2568385 := by
    simpa [prefixWord, tailWord_2568385, baseEnd_2568385] using wordTrace_append hprefix tailTrace_2568385
  have hstable : (prefixWord ++ tailWord_2568385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568385).length < 2 ^ (prefixWord ++ tailWord_2568385).sum := by decide
  have hdescent : baseEnd_2568385 < baseStart_2568385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568398 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2568398 : Nat := 118140960795 + 2568398 * 2 ^ 59
def prefixEnd_2568398 : Nat := 4983230072969 + 3 ^ 40 * 2568398 * 2
def baseEnd_2568398 : Nat := 879215124031031576475439

theorem tailTrace_2568398 : CollatzResearch.WordTrace tailWord_2568398 prefixEnd_2568398 879215124031031576475439 := by
  unfold tailWord_2568398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11709646368642521037625231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62451447299426778867334565 11709646368642521037625231)
  ·
    refine ⟨17564469552963781556437847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11709646368642521037625231 17564469552963781556437847)
    ·
      refine ⟨26346704329445672334656771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17564469552963781556437847 26346704329445672334656771)
      ·
        refine ⟨39520056494168508501985157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26346704329445672334656771 39520056494168508501985157)
        ·
          refine ⟨7410010592656595344122217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39520056494168508501985157 7410010592656595344122217)
          ·
            refine ⟨5557507944492446508091663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7410010592656595344122217 5557507944492446508091663)
            ·
              refine ⟨8336261916738669762137495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557507944492446508091663 8336261916738669762137495)
              ·
                refine ⟨12504392875108004643206243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336261916738669762137495 12504392875108004643206243)
                ·
                  refine ⟨18756589312662006964809365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12504392875108004643206243 18756589312662006964809365)
                  ·
                    refine ⟨879215124031031576475439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18756589312662006964809365 879215124031031576475439)
                    ·
                      rfl

theorem cell22_2568398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2568398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568398 prefixEnd_2568398 := by exact prefixLift 2568398
  have htrace : WordTrace (prefixWord ++ tailWord_2568398) baseStart_2568398 baseEnd_2568398 := by
    simpa [prefixWord, tailWord_2568398, baseEnd_2568398] using wordTrace_append hprefix tailTrace_2568398
  have hstable : (prefixWord ++ tailWord_2568398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568398).length < 2 ^ (prefixWord ++ tailWord_2568398).sum := by decide
  have hdescent : baseEnd_2568398 < baseStart_2568398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568413 : List Nat := [1, 4, 3, 2, 1, 2, 9]
def baseStart_2568413 : Nat := 118140960795 + 2568413 * 2 ^ 59
def prefixEnd_2568413 : Nat := 4983230072969 + 3 ^ 40 * 2568413 * 2
def baseEnd_2568413 : Nat := 32563713290280612494459

theorem tailTrace_2568413 : CollatzResearch.WordTrace tailWord_2568413 prefixEnd_2568413 32563713290280612494459 := by
  unfold tailWord_2568413
  simp only [CollatzResearch.WordTrace]
  refine ⟨93677718044085825862797893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62451812029390550575198595 93677718044085825862797893)
  ·
    refine ⟨17564572133266092349274605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93677718044085825862797893 17564572133266092349274605)
    ·
      refine ⟨6586714549974784630977977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17564572133266092349274605 6586714549974784630977977)
      ·
        refine ⟨4940035912481088473233483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6586714549974784630977977 4940035912481088473233483)
        ·
          refine ⟨7410053868721632709850225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940035912481088473233483 7410053868721632709850225)
          ·
            refine ⟨5557540401541224532387669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7410053868721632709850225 5557540401541224532387669)
            ·
              refine ⟨32563713290280612494459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5557540401541224532387669 32563713290280612494459)
              ·
                rfl

theorem cell22_2568413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 9].length) (baseStart_2568413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568413 prefixEnd_2568413 := by exact prefixLift 2568413
  have htrace : WordTrace (prefixWord ++ tailWord_2568413) baseStart_2568413 baseEnd_2568413 := by
    simpa [prefixWord, tailWord_2568413, baseEnd_2568413] using wordTrace_append hprefix tailTrace_2568413
  have hstable : (prefixWord ++ tailWord_2568413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568413).length < 2 ^ (prefixWord ++ tailWord_2568413).sum := by decide
  have hdescent : baseEnd_2568413 < baseStart_2568413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568479 : List Nat := [1, 1, 2, 4, 3, 2, 3, 2, 1, 3]
def baseStart_2568479 : Nat := 118140960795 + 2568479 * 2 ^ 59
def prefixEnd_2568479 : Nat := 4983230072969 + 3 ^ 40 * 2568479 * 2
def baseEnd_2568479 : Nat := 879242851986374365200191

theorem tailTrace_2568479 : CollatzResearch.WordTrace tailWord_2568479 prefixEnd_2568479 879242851986374365200191 := by
  unfold tailWord_2568479
  simp only [CollatzResearch.WordTrace]
  refine ⟨93680125261846719134700491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62453416841231146089800327 93680125261846719134700491)
  ·
    refine ⟨140520187892770078702050737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93680125261846719134700491 140520187892770078702050737)
    ·
      refine ⟨105390140919577559026538053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140520187892770078702050737 105390140919577559026538053)
      ·
        refine ⟨19760651422420792317475885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105390140919577559026538053 19760651422420792317475885)
        ·
          refine ⟨7410244283407797119053457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19760651422420792317475885 7410244283407797119053457)
          ·
            refine ⟨5557683212555847839290093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7410244283407797119053457 5557683212555847839290093)
            ·
              refine ⟨2084131204708442939733785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5557683212555847839290093 2084131204708442939733785)
              ·
                refine ⟨1563098403531332204800339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2084131204708442939733785 1563098403531332204800339)
                ·
                  refine ⟨2344647605296998307200509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563098403531332204800339 2344647605296998307200509)
                  ·
                    refine ⟨879242851986374365200191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344647605296998307200509 879242851986374365200191)
                    ·
                      rfl

theorem cell22_2568479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 3].length) (baseStart_2568479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568479 prefixEnd_2568479 := by exact prefixLift 2568479
  have htrace : WordTrace (prefixWord ++ tailWord_2568479) baseStart_2568479 baseEnd_2568479 := by
    simpa [prefixWord, tailWord_2568479, baseEnd_2568479] using wordTrace_append hprefix tailTrace_2568479
  have hstable : (prefixWord ++ tailWord_2568479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568479).length < 2 ^ (prefixWord ++ tailWord_2568479).sum := by decide
  have hdescent : baseEnd_2568479 < baseStart_2568479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568505 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_2568505 : Nat := 118140960795 + 2568505 * 2 ^ 59
def prefixEnd_2568505 : Nat := 4983230072969 + 3 ^ 40 * 2568505 * 2
def baseEnd_2568505 : Nat := 879251752317718964050111

theorem tailTrace_2568505 : CollatzResearch.WordTrace tailWord_2568505 prefixEnd_2568505 879251752317718964050111 := by
  unfold tailWord_2568505
  simp only [CollatzResearch.WordTrace]
  refine ⟨93681073559752525575146969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62454049039835017050097979 93681073559752525575146969)
  ·
    refine ⟨70260805169814394181360227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93681073559752525575146969 70260805169814394181360227)
    ·
      refine ⟨105391207754721591272040341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70260805169814394181360227 105391207754721591272040341)
      ·
        refine ⟨4940212863502574590876891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105391207754721591272040341 4940212863502574590876891)
        ·
          refine ⟨7410319295253861886315337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940212863502574590876891 7410319295253861886315337)
          ·
            refine ⟨5557739471440396414736503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7410319295253861886315337 5557739471440396414736503)
            ·
              refine ⟨8336609207160594622104755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557739471440396414736503 8336609207160594622104755)
              ·
                refine ⟨12504913810740891933157133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336609207160594622104755 12504913810740891933157133)
                ·
                  refine ⟨4689342679027834474933925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12504913810740891933157133 4689342679027834474933925)
                  ·
                    refine ⟨879251752317718964050111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689342679027834474933925 879251752317718964050111)
                    ·
                      rfl

theorem cell22_2568505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_2568505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568505 prefixEnd_2568505 := by exact prefixLift 2568505
  have htrace : WordTrace (prefixWord ++ tailWord_2568505) baseStart_2568505 baseEnd_2568505 := by
    simpa [prefixWord, tailWord_2568505, baseEnd_2568505] using wordTrace_append hprefix tailTrace_2568505
  have hstable : (prefixWord ++ tailWord_2568505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568505).length < 2 ^ (prefixWord ++ tailWord_2568505).sum := by decide
  have hdescent : baseEnd_2568505 < baseStart_2568505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568552 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 2, 3]
def baseStart_2568552 : Nat := 118140960795 + 2568552 * 2 ^ 59
def prefixEnd_2568552 : Nat := 4983230072969 + 3 ^ 40 * 2568552 * 2
def baseEnd_2568552 : Nat := 879267841378226508124967

theorem tailTrace_2568552 : CollatzResearch.WordTrace tailWord_2568552 prefixEnd_2568552 879267841378226508124967 := by
  unfold tailWord_2568552
  simp only [CollatzResearch.WordTrace]
  refine ⟨46841393895291126301053955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62455191860388168401405273 46841393895291126301053955)
  ·
    refine ⟨70262090842936689451580933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46841393895291126301053955 70262090842936689451580933)
    ·
      refine ⟨13174142033050629272171425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70262090842936689451580933 13174142033050629272171425)
      ·
        refine ⟨9880606524787971954128569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13174142033050629272171425 9880606524787971954128569)
        ·
          refine ⟨7410454893590978965596427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9880606524787971954128569 7410454893590978965596427)
          ·
            refine ⟨11115682340386468448394641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410454893590978965596427 11115682340386468448394641)
            ·
              refine ⟨8336761755289851336295981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11115682340386468448394641 8336761755289851336295981)
              ·
                refine ⟨3126285658233694251110993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8336761755289851336295981 3126285658233694251110993)
                ·
                  refine ⟨2344714243675270688333245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126285658233694251110993 2344714243675270688333245)
                  ·
                    refine ⟨879267841378226508124967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344714243675270688333245 879267841378226508124967)
                    ·
                      rfl

theorem cell22_2568552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_2568552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568552 prefixEnd_2568552 := by exact prefixLift 2568552
  have htrace : WordTrace (prefixWord ++ tailWord_2568552) baseStart_2568552 baseEnd_2568552 := by
    simpa [prefixWord, tailWord_2568552, baseEnd_2568552] using wordTrace_append hprefix tailTrace_2568552
  have hstable : (prefixWord ++ tailWord_2568552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568552).length < 2 ^ (prefixWord ++ tailWord_2568552).sum := by decide
  have hdescent : baseEnd_2568552 < baseStart_2568552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568580 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2568580 : Nat := 118140960795 + 2568580 * 2 ^ 59
def prefixEnd_2568580 : Nat := 4983230072969 + 3 ^ 40 * 2568580 * 2
def baseEnd_2568580 : Nat := 879277426350443768424881

theorem tailTrace_2568580 : CollatzResearch.WordTrace tailWord_2568580 prefixEnd_2568580 879277426350443768424881 := by
  unfold tailWord_2568580
  simp only [CollatzResearch.WordTrace]
  refine ⟨46841904517240406692063597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62455872689653875589418129 46841904517240406692063597)
  ·
    refine ⟨17565714193965152509523849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46841904517240406692063597 17565714193965152509523849)
    ·
      refine ⟨13174285645473864382142887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17565714193965152509523849 13174285645473864382142887)
      ·
        refine ⟨19761428468210796573214331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13174285645473864382142887 19761428468210796573214331)
        ·
          refine ⟨29642142702316194859821497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19761428468210796573214331 29642142702316194859821497)
          ·
            refine ⟨22231607026737146144866123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29642142702316194859821497 22231607026737146144866123)
            ·
              refine ⟨33347410540105719217299185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22231607026737146144866123 33347410540105719217299185)
              ·
                refine ⟨25010557905079289412974389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33347410540105719217299185 25010557905079289412974389)
                ·
                  refine ⟨2344739803601183382466349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25010557905079289412974389 2344739803601183382466349)
                  ·
                    refine ⟨879277426350443768424881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344739803601183382466349 879277426350443768424881)
                    ·
                      rfl

theorem cell22_2568580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2568580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568580 prefixEnd_2568580 := by exact prefixLift 2568580
  have htrace : WordTrace (prefixWord ++ tailWord_2568580) baseStart_2568580 baseEnd_2568580 := by
    simpa [prefixWord, tailWord_2568580, baseEnd_2568580] using wordTrace_append hprefix tailTrace_2568580
  have hstable : (prefixWord ++ tailWord_2568580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568580).length < 2 ^ (prefixWord ++ tailWord_2568580).sum := by decide
  have hdescent : baseEnd_2568580 < baseStart_2568580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568586 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_2568586 : Nat := 118140960795 + 2568586 * 2 ^ 59
def prefixEnd_2568586 : Nat := 4983230072969 + 3 ^ 40 * 2568586 * 2
def baseEnd_2568586 : Nat := 879279480273061752774863

theorem tailTrace_2568586 : CollatzResearch.WordTrace tailWord_2568586 prefixEnd_2568586 879279480273061752774863 := by
  unfold tailWord_2568586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23421006968114769102211403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62456018581639384272563741 23421006968114769102211403)
  ·
    refine ⟨35131510452172153653317105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23421006968114769102211403 35131510452172153653317105)
    ·
      refine ⟨26348632839129115239987829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35131510452172153653317105 26348632839129115239987829)
      ·
        refine ⟨2470184328668354553748859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26348632839129115239987829 2470184328668354553748859)
        ·
          refine ⟨3705276493002531830623289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470184328668354553748859 3705276493002531830623289)
          ·
            refine ⟨2778957369751898872967467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3705276493002531830623289 2778957369751898872967467)
            ·
              refine ⟨4168436054627848309451201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778957369751898872967467 4168436054627848309451201)
              ·
                refine ⟨3126327040970886232088401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168436054627848309451201 3126327040970886232088401)
                ·
                  refine ⟨2344745280728164674066301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126327040970886232088401 2344745280728164674066301)
                  ·
                    refine ⟨879279480273061752774863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344745280728164674066301 879279480273061752774863)
                    ·
                      rfl

theorem cell22_2568586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_2568586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568586 prefixEnd_2568586 := by exact prefixLift 2568586
  have htrace : WordTrace (prefixWord ++ tailWord_2568586) baseStart_2568586 baseEnd_2568586 := by
    simpa [prefixWord, tailWord_2568586, baseEnd_2568586] using wordTrace_append hprefix tailTrace_2568586
  have hstable : (prefixWord ++ tailWord_2568586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568586).length < 2 ^ (prefixWord ++ tailWord_2568586).sum := by decide
  have hdescent : baseEnd_2568586 < baseStart_2568586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568683 : List Nat := [1, 1, 1, 1, 2, 3, 3, 10]
def baseStart_2568683 : Nat := 118140960795 + 2568683 * 2 ^ 59
def prefixEnd_2568683 : Nat := 4983230072969 + 3 ^ 40 * 2568683 * 2
def baseEnd_2568683 : Nat := 97701409483931759233285

theorem tailTrace_2568683 : CollatzResearch.WordTrace tailWord_2568683 prefixEnd_2568683 97701409483931759233285 := by
  unfold tailWord_2568683
  simp only [CollatzResearch.WordTrace]
  refine ⟨93687565753107661975126703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62458377168738441316751135 93687565753107661975126703)
  ·
    refine ⟨140531348629661492962690055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93687565753107661975126703 140531348629661492962690055)
    ·
      refine ⟨210797022944492239444035083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140531348629661492962690055 210797022944492239444035083)
      ·
        refine ⟨316195534416738359166052625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210797022944492239444035083 316195534416738359166052625)
        ·
          refine ⟨237146650812553769374539469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316195534416738359166052625 237146650812553769374539469)
          ·
            refine ⟨88929994054707663515452301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237146650812553769374539469 88929994054707663515452301)
            ·
              refine ⟨33348747770515373818294613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88929994054707663515452301 33348747770515373818294613)
              ·
                refine ⟨97701409483931759233285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33348747770515373818294613 97701409483931759233285)
                ·
                  rfl

theorem cell22_2568683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 10].length) (baseStart_2568683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568683 prefixEnd_2568683 := by exact prefixLift 2568683
  have htrace : WordTrace (prefixWord ++ tailWord_2568683) baseStart_2568683 baseEnd_2568683 := by
    simpa [prefixWord, tailWord_2568683, baseEnd_2568683] using wordTrace_append hprefix tailTrace_2568683
  have hstable : (prefixWord ++ tailWord_2568683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568683).length < 2 ^ (prefixWord ++ tailWord_2568683).sum := by decide
  have hdescent : baseEnd_2568683 < baseStart_2568683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568706 : List Nat := [3, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2568706 : Nat := 118140960795 + 2568706 * 2 ^ 59
def prefixEnd_2568706 : Nat := 4983230072969 + 3 ^ 40 * 2568706 * 2
def baseEnd_2568706 : Nat := 293106852908473813258165

theorem tailTrace_2568706 : CollatzResearch.WordTrace tailWord_2568706 prefixEnd_2568706 293106852908473813258165 := by
  unfold tailWord_2568706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23422101158006084225803493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62458936421349557935475981 23422101158006084225803493)
  ·
    refine ⟨4391643967126140792338155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23422101158006084225803493 4391643967126140792338155)
    ·
      refine ⟨6587465950689211188507233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4391643967126140792338155 6587465950689211188507233)
      ·
        refine ⟨4940599463016908391380425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6587465950689211188507233 4940599463016908391380425)
        ·
          refine ⟨3705449597262681293535319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4940599463016908391380425 3705449597262681293535319)
          ·
            refine ⟨5558174395894021940302979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705449597262681293535319 5558174395894021940302979)
            ·
              refine ⟨8337261593841032910454469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5558174395894021940302979 8337261593841032910454469)
              ·
                refine ⟨1563236548845193670710213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8337261593841032910454469 1563236548845193670710213)
                ·
                  refine ⟨293106852908473813258165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1563236548845193670710213 293106852908473813258165)
                  ·
                    rfl

theorem cell22_2568706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2568706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568706 prefixEnd_2568706 := by exact prefixLift 2568706
  have htrace : WordTrace (prefixWord ++ tailWord_2568706) baseStart_2568706 baseEnd_2568706 := by
    simpa [prefixWord, tailWord_2568706, baseEnd_2568706] using wordTrace_append hprefix tailTrace_2568706
  have hstable : (prefixWord ++ tailWord_2568706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568706).length < 2 ^ (prefixWord ++ tailWord_2568706).sum := by decide
  have hdescent : baseEnd_2568706 < baseStart_2568706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568732 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_2568732 : Nat := 118140960795 + 2568732 * 2 ^ 59
def prefixEnd_2568732 : Nat := 4983230072969 + 3 ^ 40 * 2568732 * 2
def baseEnd_2568732 : Nat := 879329459056766038624415

theorem tailTrace_2568732 : CollatzResearch.WordTrace tailWord_2568732 prefixEnd_2568732 879329459056766038624415 := by
  unfold tailWord_2568732
  simp only [CollatzResearch.WordTrace]
  refine ⟨46844676464965071671830225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62459568619953428895773633 46844676464965071671830225)
  ·
    refine ⟨35133507348723803753872669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46844676464965071671830225 35133507348723803753872669)
    ·
      refine ⟨13175065255771426407702251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35133507348723803753872669 13175065255771426407702251)
      ·
        refine ⟨19762597883657139611553377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13175065255771426407702251 19762597883657139611553377)
        ·
          refine ⟨14821948412742854708665033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19762597883657139611553377 14821948412742854708665033)
          ·
            refine ⟨11116461309557141031498775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14821948412742854708665033 11116461309557141031498775)
            ·
              refine ⟨16674691964335711547248163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11116461309557141031498775 16674691964335711547248163)
              ·
                refine ⟨25012037946503567320872245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16674691964335711547248163 25012037946503567320872245)
                ·
                  refine ⟨2344878557484709436331773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25012037946503567320872245 2344878557484709436331773)
                  ·
                    refine ⟨879329459056766038624415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344878557484709436331773 879329459056766038624415)
                    ·
                      rfl

theorem cell22_2568732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_2568732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568732 prefixEnd_2568732 := by exact prefixLift 2568732
  have htrace : WordTrace (prefixWord ++ tailWord_2568732) baseStart_2568732 baseEnd_2568732 := by
    simpa [prefixWord, tailWord_2568732, baseEnd_2568732] using wordTrace_append hprefix tailTrace_2568732
  have hstable : (prefixWord ++ tailWord_2568732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568732).length < 2 ^ (prefixWord ++ tailWord_2568732).sum := by decide
  have hdescent : baseEnd_2568732 < baseStart_2568732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568736 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 2, 4]
def baseStart_2568736 : Nat := 118140960795 + 2568736 * 2 ^ 59
def prefixEnd_2568736 : Nat := 4983230072969 + 3 ^ 40 * 2568736 * 2
def baseEnd_2568736 : Nat := 879330828338511361524403

theorem tailTrace_2568736 : CollatzResearch.WordTrace tailWord_2568736 prefixEnd_2568736 879330828338511361524403 := by
  unfold tailWord_2568736
  simp only [CollatzResearch.WordTrace]
  refine ⟨46844749410957826013403031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62459665881277101351204041 46844749410957826013403031)
  ·
    refine ⟨70267124116436739020104547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46844749410957826013403031 70267124116436739020104547)
    ·
      refine ⟨105400686174655108530156821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70267124116436739020104547 105400686174655108530156821)
      ·
        refine ⟨4940657164436958212351101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105400686174655108530156821 4940657164436958212351101)
        ·
          refine ⟨1852746436663859329631663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4940657164436958212351101 1852746436663859329631663)
          ·
            refine ⟨2779119654995788994447495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852746436663859329631663 2779119654995788994447495)
            ·
              refine ⟨4168679482493683491671243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779119654995788994447495 4168679482493683491671243)
              ·
                refine ⟨6253019223740525237506865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168679482493683491671243 6253019223740525237506865)
                ·
                  refine ⟨4689764417805393928130149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6253019223740525237506865 4689764417805393928130149)
                  ·
                    refine ⟨879330828338511361524403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689764417805393928130149 879330828338511361524403)
                    ·
                      rfl

theorem cell22_2568736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_2568736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568736 prefixEnd_2568736 := by exact prefixLift 2568736
  have htrace : WordTrace (prefixWord ++ tailWord_2568736) baseStart_2568736 baseEnd_2568736 := by
    simpa [prefixWord, tailWord_2568736, baseEnd_2568736] using wordTrace_append hprefix tailTrace_2568736
  have hstable : (prefixWord ++ tailWord_2568736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568736).length < 2 ^ (prefixWord ++ tailWord_2568736).sum := by decide
  have hdescent : baseEnd_2568736 < baseStart_2568736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568760 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_2568760 : Nat := 118140960795 + 2568760 * 2 ^ 59
def prefixEnd_2568760 : Nat := 4983230072969 + 3 ^ 40 * 2568760 * 2
def baseEnd_2568760 : Nat := 879339044028983298924329

theorem tailTrace_2568760 : CollatzResearch.WordTrace tailWord_2568760 prefixEnd_2568760 879339044028983298924329 := by
  unfold tailWord_2568760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46845187086914352062839867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62460249449219136083786489 46845187086914352062839867)
  ·
    refine ⟨70267780630371528094259801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46845187086914352062839867 70267780630371528094259801)
    ·
      refine ⟨52700835472778646070694851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70267780630371528094259801 52700835472778646070694851)
      ·
        refine ⟨79051253209167969106042277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52700835472778646070694851 79051253209167969106042277)
        ·
          refine ⟨14822109976718994207382927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79051253209167969106042277 14822109976718994207382927)
          ·
            refine ⟨22233164965078491311074391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14822109976718994207382927 22233164965078491311074391)
            ·
              refine ⟨33349747447617736966611587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22233164965078491311074391 33349747447617736966611587)
              ·
                refine ⟨50024621171426605449917381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33349747447617736966611587 50024621171426605449917381)
                ·
                  refine ⟨9379616469642488521859509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50024621171426605449917381 9379616469642488521859509)
                  ·
                    refine ⟨879339044028983298924329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9379616469642488521859509 879339044028983298924329)
                    ·
                      rfl

theorem cell22_2568760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_2568760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568760 prefixEnd_2568760 := by exact prefixLift 2568760
  have htrace : WordTrace (prefixWord ++ tailWord_2568760) baseStart_2568760 baseEnd_2568760 := by
    simpa [prefixWord, tailWord_2568760, baseEnd_2568760] using wordTrace_append hprefix tailTrace_2568760
  have hstable : (prefixWord ++ tailWord_2568760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568760).length < 2 ^ (prefixWord ++ tailWord_2568760).sum := by decide
  have hdescent : baseEnd_2568760 < baseStart_2568760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568762 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_2568762 : Nat := 118140960795 + 2568762 * 2 ^ 59
def prefixEnd_2568762 : Nat := 4983230072969 + 3 ^ 40 * 2568762 * 2
def baseEnd_2568762 : Nat := 293113242889951986791441

theorem tailTrace_2568762 : CollatzResearch.WordTrace tailWord_2568762 prefixEnd_2568762 293113242889951986791441 := by
  unfold tailWord_2568762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23422611779955364616813135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62460298079880972311501693 23422611779955364616813135)
  ·
    refine ⟨35133917669933046925219703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23422611779955364616813135 35133917669933046925219703)
    ·
      refine ⟨52700876504899570387829555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35133917669933046925219703 52700876504899570387829555)
      ·
        refine ⟨79051314757349355581744333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52700876504899570387829555 79051314757349355581744333)
        ·
          refine ⟨29644243034006008343154125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79051314757349355581744333 29644243034006008343154125)
          ·
            refine ⟨11116591137752253128682797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29644243034006008343154125 11116591137752253128682797)
            ·
              refine ⟨4168721676657094923256049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11116591137752253128682797 4168721676657094923256049)
              ·
                refine ⟨3126541257492821192442037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168721676657094923256049 3126541257492821192442037)
                ·
                  refine ⟨293113242889951986791441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126541257492821192442037 293113242889951986791441)
                  ·
                    rfl

theorem cell22_2568762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_2568762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568762 prefixEnd_2568762 := by exact prefixLift 2568762
  have htrace : WordTrace (prefixWord ++ tailWord_2568762) baseStart_2568762 baseEnd_2568762 := by
    simpa [prefixWord, tailWord_2568762, baseEnd_2568762] using wordTrace_append hprefix tailTrace_2568762
  have hstable : (prefixWord ++ tailWord_2568762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568762).length < 2 ^ (prefixWord ++ tailWord_2568762).sum := by decide
  have hdescent : baseEnd_2568762 < baseStart_2568762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
