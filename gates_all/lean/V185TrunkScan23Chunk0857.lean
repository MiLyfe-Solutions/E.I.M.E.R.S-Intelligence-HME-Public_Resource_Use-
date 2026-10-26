import V185TrunkScan23Chunk0856

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5071886 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_5071886 : Nat := 118140960795 + 5071886 * 2 ^ 59
def prefixEnd_5071886 : Nat := 4983230072969 + 3 ^ 40 * 5071886 * 2
def baseEnd_5071886 : Nat := 2604315342809648456399827

theorem tailTrace_5071886 : CollatzResearch.WordTrace tailWord_5071886 prefixEnd_5071886 2604315342809648456399827 := by
  unfold tailWord_5071886
  simp only [CollatzResearch.WordTrace]
  refine ⟨23123359962928838251434439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123324586468953804007650341 23123359962928838251434439)
  ·
    refine ⟨34685039944393257377151659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23123359962928838251434439 34685039944393257377151659)
    ·
      refine ⟨52027559916589886065727489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34685039944393257377151659 52027559916589886065727489)
      ·
        refine ⟨39020669937442414549295617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52027559916589886065727489 39020669937442414549295617)
        ·
          refine ⟨29265502453081810911971713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39020669937442414549295617 29265502453081810911971713)
          ·
            refine ⟨21949126839811358183978785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29265502453081810911971713 21949126839811358183978785)
            ·
              refine ⟨16461845129858518637984089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21949126839811358183978785 16461845129858518637984089)
              ·
                refine ⟨12346383847393888978488067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16461845129858518637984089 12346383847393888978488067)
                ·
                  refine ⟨18519575771090833467732101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12346383847393888978488067 18519575771090833467732101)
                  ·
                    refine ⟨3472420457079531275199769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18519575771090833467732101 3472420457079531275199769)
                    ·
                      refine ⟨2604315342809648456399827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472420457079531275199769 2604315342809648456399827)
                      ·
                        rfl

theorem cell23_5071886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_5071886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071886 prefixEnd_5071886 := by exact prefixLift 5071886
  have htrace : WordTrace (prefixWord ++ tailWord_5071886) baseStart_5071886 baseEnd_5071886 := by
    simpa [prefixWord, tailWord_5071886, baseEnd_5071886] using wordTrace_append hprefix tailTrace_5071886
  have hstable : (prefixWord ++ tailWord_5071886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071886).length < 2 ^ (prefixWord ++ tailWord_5071886).sum := by decide
  have hdescent : baseEnd_5071886 < baseStart_5071886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071903 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 2, 2, 2]
def baseStart_5071903 : Nat := 118140960795 + 5071903 * 2 ^ 59
def prefixEnd_5071903 : Nat := 4983230072969 + 3 ^ 40 * 5071903 * 2
def baseEnd_5071903 : Nat := 2604324071980774889887249

theorem tailTrace_5071903 : CollatzResearch.WordTrace tailWord_5071903 prefixEnd_5071903 2604324071980774889887249 := by
  unfold tailWord_5071903
  simp only [CollatzResearch.WordTrace]
  refine ⟨184987499744369117914844363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123324999829579411943229575 184987499744369117914844363)
  ·
    refine ⟨277481249616553676872266545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184987499744369117914844363 277481249616553676872266545)
    ·
      refine ⟨208110937212415257654199909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277481249616553676872266545 208110937212415257654199909)
      ·
        refine ⟨39020800727327860810162483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208110937212415257654199909 39020800727327860810162483)
        ·
          refine ⟨58531201090991791215243725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39020800727327860810162483 58531201090991791215243725)
          ·
            refine ⟨21949200409121921705716397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58531201090991791215243725 21949200409121921705716397)
            ·
              refine ⟨8230950153420720639643649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21949200409121921705716397 8230950153420720639643649)
              ·
                refine ⟨6173212615065540479732737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8230950153420720639643649 6173212615065540479732737)
                ·
                  refine ⟨4629909461299155359799553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6173212615065540479732737 4629909461299155359799553)
                  ·
                    refine ⟨3472432095974366519849665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4629909461299155359799553 3472432095974366519849665)
                    ·
                      refine ⟨2604324071980774889887249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472432095974366519849665 2604324071980774889887249)
                      ·
                        rfl

theorem cell23_5071903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_5071903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071903 prefixEnd_5071903 := by exact prefixLift 5071903
  have htrace : WordTrace (prefixWord ++ tailWord_5071903) baseStart_5071903 baseEnd_5071903 := by
    simpa [prefixWord, tailWord_5071903, baseEnd_5071903] using wordTrace_append hprefix tailTrace_5071903
  have hstable : (prefixWord ++ tailWord_5071903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071903).length < 2 ^ (prefixWord ++ tailWord_5071903).sum := by decide
  have hdescent : baseEnd_5071903 < baseStart_5071903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071909 : List Nat := [1, 3, 1, 2, 2, 2, 1, 6, 5]
def baseStart_5071909 : Nat := 118140960795 + 5071909 * 2 ^ 59
def prefixEnd_5071909 : Nat := 4983230072969 + 3 ^ 40 * 5071909 * 2
def baseEnd_5071909 : Nat := 289369683651633540712469

theorem tailTrace_5071909 : CollatzResearch.WordTrace tailWord_5071909 prefixEnd_5071909 289369683651633540712469 := by
  unfold tailWord_5071909
  simp only [CollatzResearch.WordTrace]
  refine ⟨184987718582347380939562781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123325145721564920626375187 184987718582347380939562781)
  ·
    refine ⟨69370394468380267852336043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184987718582347380939562781 69370394468380267852336043)
    ·
      refine ⟨104055591702570401778504065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69370394468380267852336043 104055591702570401778504065)
      ·
        refine ⟨78041693776927801333878049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104055591702570401778504065 78041693776927801333878049)
        ·
          refine ⟨58531270332695851000408537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78041693776927801333878049 58531270332695851000408537)
          ·
            refine ⟨43898452749521888250306403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58531270332695851000408537 43898452749521888250306403)
            ·
              refine ⟨65847679124282832375459605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43898452749521888250306403 65847679124282832375459605)
              ·
                refine ⟨3086609958950757767599669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65847679124282832375459605 3086609958950757767599669)
                ·
                  refine ⟨289369683651633540712469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3086609958950757767599669 289369683651633540712469)
                  ·
                    rfl

theorem cell23_5071909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_5071909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071909 prefixEnd_5071909 := by exact prefixLift 5071909
  have htrace : WordTrace (prefixWord ++ tailWord_5071909) baseStart_5071909 baseEnd_5071909 := by
    simpa [prefixWord, tailWord_5071909, baseEnd_5071909] using wordTrace_append hprefix tailTrace_5071909
  have hstable : (prefixWord ++ tailWord_5071909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071909).length < 2 ^ (prefixWord ++ tailWord_5071909).sum := by decide
  have hdescent : baseEnd_5071909 < baseStart_5071909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071922 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_5071922 : Nat := 118140960795 + 5071922 * 2 ^ 59
def prefixEnd_5071922 : Nat := 4983230072969 + 3 ^ 40 * 5071922 * 2
def baseEnd_5071922 : Nat := 868111276037736771849887

theorem tailTrace_5071922 : CollatzResearch.WordTrace tailWord_5071922 prefixEnd_5071922 868111276037736771849887 := by
  unfold tailWord_5071922
  simp only [CollatzResearch.WordTrace]
  refine ⟨46247048182825071039946505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123325461820866856106524013 46247048182825071039946505)
  ·
    refine ⟨34685286137118803279959879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46247048182825071039946505 34685286137118803279959879)
    ·
      refine ⟨52027929205678204919939819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34685286137118803279959879 52027929205678204919939819)
      ·
        refine ⟨78041893808517307379909729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52027929205678204919939819 78041893808517307379909729)
        ·
          refine ⟨58531420356387980534932297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78041893808517307379909729 58531420356387980534932297)
          ·
            refine ⟨43898565267290985401199223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58531420356387980534932297 43898565267290985401199223)
            ·
              refine ⟨65847847900936478101798835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43898565267290985401199223 65847847900936478101798835)
              ·
                refine ⟨98771771851404717152698253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65847847900936478101798835 98771771851404717152698253)
                ·
                  refine ⟨37039414444276768932261845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98771771851404717152698253 37039414444276768932261845)
                  ·
                    refine ⟨868111276037736771849887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37039414444276768932261845 868111276037736771849887)
                    ·
                      rfl

theorem cell23_5071922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_5071922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071922 prefixEnd_5071922 := by exact prefixLift 5071922
  have htrace : WordTrace (prefixWord ++ tailWord_5071922) baseStart_5071922 baseEnd_5071922 := by
    simpa [prefixWord, tailWord_5071922, baseEnd_5071922] using wordTrace_append hprefix tailTrace_5071922
  have hstable : (prefixWord ++ tailWord_5071922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071922).length < 2 ^ (prefixWord ++ tailWord_5071922).sum := by decide
  have hdescent : baseEnd_5071922 < baseStart_5071922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071962 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_5071962 : Nat := 118140960795 + 5071962 * 2 ^ 59
def prefixEnd_5071962 : Nat := 4983230072969 + 3 ^ 40 * 5071962 * 2
def baseEnd_5071962 : Nat := 2604354367339390159049477

theorem tailTrace_5071962 : CollatzResearch.WordTrace tailWord_5071962 prefixEnd_5071962 2604354367339390159049477 := by
  unfold tailWord_5071962
  simp only [CollatzResearch.WordTrace]
  refine ⟨46247412912788842747810535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123326434434103580660828093 46247412912788842747810535)
  ·
    refine ⟨69371119369183264121715803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46247412912788842747810535 69371119369183264121715803)
    ·
      refine ⟨104056679053774896182573705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69371119369183264121715803 104056679053774896182573705)
      ·
        refine ⟨78042509290331172136930279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104056679053774896182573705 78042509290331172136930279)
        ·
          refine ⟨117063763935496758205395419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78042509290331172136930279 117063763935496758205395419)
          ·
            refine ⟨175595645903245137308093129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117063763935496758205395419 175595645903245137308093129)
            ·
              refine ⟨131696734427433852981069847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175595645903245137308093129 131696734427433852981069847)
              ·
                refine ⟨197545101641150779471604771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131696734427433852981069847 197545101641150779471604771)
                ·
                  refine ⟨296317652461726169207407157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197545101641150779471604771 296317652461726169207407157)
                  ·
                    refine ⟨27779779918286828363194421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 296317652461726169207407157 27779779918286828363194421)
                    ·
                      refine ⟨2604354367339390159049477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27779779918286828363194421 2604354367339390159049477)
                      ·
                        rfl

theorem cell23_5071962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_5071962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071962 prefixEnd_5071962 := by exact prefixLift 5071962
  have htrace : WordTrace (prefixWord ++ tailWord_5071962) baseStart_5071962 baseEnd_5071962 := by
    simpa [prefixWord, tailWord_5071962, baseEnd_5071962] using wordTrace_append hprefix tailTrace_5071962
  have hstable : (prefixWord ++ tailWord_5071962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071962).length < 2 ^ (prefixWord ++ tailWord_5071962).sum := by decide
  have hdescent : baseEnd_5071962 < baseStart_5071962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071996 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_5071996 : Nat := 118140960795 + 5071996 * 2 ^ 59
def prefixEnd_5071996 : Nat := 4983230072969 + 3 ^ 40 * 5071996 * 2
def baseEnd_5071996 : Nat := 2604371825681643026024321

theorem tailTrace_5071996 : CollatzResearch.WordTrace tailWord_5071996 prefixEnd_5071996 2604371825681643026024321 := by
  unfold tailWord_5071996
  simp only [CollatzResearch.WordTrace]
  refine ⟨92495445866516097398989921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123327261155354796531986561 92495445866516097398989921)
  ·
    refine ⟨69371584399887073049242441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92495445866516097398989921 69371584399887073049242441)
    ·
      refine ⟨52028688299915304786931831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69371584399887073049242441 52028688299915304786931831)
      ·
        refine ⟨78043032449872957180397747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52028688299915304786931831 78043032449872957180397747)
        ·
          refine ⟨117064548674809435770596621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78043032449872957180397747 117064548674809435770596621)
          ·
            refine ⟨43899205753053538413973733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117064548674809435770596621 43899205753053538413973733)
            ·
              refine ⟨8231101078697538452620075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43899205753053538413973733 8231101078697538452620075)
              ·
                refine ⟨12346651618046307678930113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8231101078697538452620075 12346651618046307678930113)
                ·
                  refine ⟨9259988713534730759197585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12346651618046307678930113 9259988713534730759197585)
                  ·
                    refine ⟨6944991535151048069398189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9259988713534730759197585 6944991535151048069398189)
                    ·
                      refine ⟨2604371825681643026024321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6944991535151048069398189 2604371825681643026024321)
                      ·
                        rfl

theorem cell23_5071996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_5071996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071996 prefixEnd_5071996 := by exact prefixLift 5071996
  have htrace : WordTrace (prefixWord ++ tailWord_5071996) baseStart_5071996 baseEnd_5071996 := by
    simpa [prefixWord, tailWord_5071996, baseEnd_5071996] using wordTrace_append hprefix tailTrace_5071996
  have hstable : (prefixWord ++ tailWord_5071996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071996).length < 2 ^ (prefixWord ++ tailWord_5071996).sum := by decide
  have hdescent : baseEnd_5071996 < baseStart_5071996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072029 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_5072029 : Nat := 118140960795 + 5072029 * 2 ^ 59
def prefixEnd_5072029 : Nat := 4983230072969 + 3 ^ 40 * 5072029 * 2
def baseEnd_5072029 : Nat := 868129590181080465637223

theorem tailTrace_5072029 : CollatzResearch.WordTrace tailWord_5072029 prefixEnd_5072029 868129590181080465637223 := by
  unfold tailWord_5072029
  simp only [CollatzResearch.WordTrace]
  refine ⟨184992095341912641433931141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123328063561275094289287427 184992095341912641433931141)
  ·
    refine ⟨34686017876608620268862089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184992095341912641433931141 34686017876608620268862089)
    ·
      refine ⟨26014513407456465201646567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34686017876608620268862089 26014513407456465201646567)
      ·
        refine ⟨39021770111184697802469851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26014513407456465201646567 39021770111184697802469851)
        ·
          refine ⟨58532655166777046703704777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39021770111184697802469851 58532655166777046703704777)
          ·
            refine ⟨43899491375082785027778583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58532655166777046703704777 43899491375082785027778583)
            ·
              refine ⟨65849237062624177541667875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43899491375082785027778583 65849237062624177541667875)
              ·
                refine ⟨98773855593936266312501813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65849237062624177541667875 98773855593936266312501813)
                ·
                  refine ⟨9260048961931524966797045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98773855593936266312501813 9260048961931524966797045)
                  ·
                    refine ⟨868129590181080465637223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9260048961931524966797045 868129590181080465637223)
                    ·
                      rfl

theorem cell23_5072029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_5072029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072029 prefixEnd_5072029 := by exact prefixLift 5072029
  have htrace : WordTrace (prefixWord ++ tailWord_5072029) baseStart_5072029 baseEnd_5072029 := by
    simpa [prefixWord, tailWord_5072029, baseEnd_5072029] using wordTrace_append hprefix tailTrace_5072029
  have hstable : (prefixWord ++ tailWord_5072029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072029).length < 2 ^ (prefixWord ++ tailWord_5072029).sum := by decide
  have hdescent : baseEnd_5072029 < baseStart_5072029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072054 : List Nat := [5, 1, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5072054 : Nat := 118140960795 + 5072054 * 2 ^ 59
def prefixEnd_5072054 : Nat := 4983230072969 + 3 ^ 40 * 5072054 * 2
def baseEnd_5072054 : Nat := 868133869186534599699685

theorem tailTrace_5072054 : CollatzResearch.WordTrace tailWord_5072054 prefixEnd_5072054 868133869186534599699685 := by
  unfold tailWord_5072054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562062947926379418974451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123328671444548047135727477 11562062947926379418974451)
  ·
    refine ⟨17343094421889569128461677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11562062947926379418974451 17343094421889569128461677)
    ·
      refine ⟨6503660408208588423173129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17343094421889569128461677 6503660408208588423173129)
      ·
        refine ⟨4877745306156441317379847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6503660408208588423173129 4877745306156441317379847)
        ·
          refine ⟨7316617959234661976069771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877745306156441317379847 7316617959234661976069771)
          ·
            refine ⟨10974926938851992964104657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7316617959234661976069771 10974926938851992964104657)
            ·
              refine ⟨8231195204138994723078493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10974926938851992964104657 8231195204138994723078493)
              ·
                refine ⟨3086698201552123021154435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8231195204138994723078493 3086698201552123021154435)
                ·
                  refine ⟨4630047302328184531731653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3086698201552123021154435 4630047302328184531731653)
                  ·
                    refine ⟨868133869186534599699685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630047302328184531731653 868133869186534599699685)
                    ·
                      rfl

theorem cell23_5072054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5072054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072054 prefixEnd_5072054 := by exact prefixLift 5072054
  have htrace : WordTrace (prefixWord ++ tailWord_5072054) baseStart_5072054 baseEnd_5072054 := by
    simpa [prefixWord, tailWord_5072054, baseEnd_5072054] using wordTrace_append hprefix tailTrace_5072054
  have hstable : (prefixWord ++ tailWord_5072054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072054).length < 2 ^ (prefixWord ++ tailWord_5072054).sum := by decide
  have hdescent : baseEnd_5072054 < baseStart_5072054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072060 : List Nat := [2, 2, 2, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_5072060 : Nat := 118140960795 + 5072060 * 2 ^ 59
def prefixEnd_5072060 : Nat := 4983230072969 + 3 ^ 40 * 5072060 * 2
def baseEnd_5072060 : Nat := 2604404688443530775624027

theorem tailTrace_5072060 : CollatzResearch.WordTrace tailWord_5072060 prefixEnd_5072060 2604404688443530775624027 := by
  unfold tailWord_5072060
  simp only [CollatzResearch.WordTrace]
  refine ⟨92496613002400166864154817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123328817336533555818873089 92496613002400166864154817)
  ·
    refine ⟨69372459751800125148116113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92496613002400166864154817 69372459751800125148116113)
    ·
      refine ⟨52029344813850093861087085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69372459751800125148116113 52029344813850093861087085)
      ·
        refine ⟨19511004305193785197907657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52029344813850093861087085 19511004305193785197907657)
        ·
          refine ⟨14633253228895338898430743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19511004305193785197907657 14633253228895338898430743)
          ·
            refine ⟨21949879843343008347646115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14633253228895338898430743 21949879843343008347646115)
            ·
              refine ⟨32924819765014512521469173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21949879843343008347646115 32924819765014512521469173)
              ·
                refine ⟨3086701852970110548887735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32924819765014512521469173 3086701852970110548887735)
                ·
                  refine ⟨4630052779455165823331603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3086701852970110548887735 4630052779455165823331603)
                  ·
                    refine ⟨6945079169182748734997405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4630052779455165823331603 6945079169182748734997405)
                    ·
                      refine ⟨2604404688443530775624027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6945079169182748734997405 2604404688443530775624027)
                      ·
                        rfl

theorem cell23_5072060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_5072060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072060 prefixEnd_5072060 := by exact prefixLift 5072060
  have htrace : WordTrace (prefixWord ++ tailWord_5072060) baseStart_5072060 baseEnd_5072060 := by
    simpa [prefixWord, tailWord_5072060, baseEnd_5072060] using wordTrace_append hprefix tailTrace_5072060
  have hstable : (prefixWord ++ tailWord_5072060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072060).length < 2 ^ (prefixWord ++ tailWord_5072060).sum := by decide
  have hdescent : baseEnd_5072060 < baseStart_5072060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072069 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_5072069 : Nat := 118140960795 + 5072069 * 2 ^ 59
def prefixEnd_5072069 : Nat := 4983230072969 + 3 ^ 40 * 5072069 * 2
def baseEnd_5072069 : Nat := 2604409309769421240411485

theorem tailTrace_5072069 : CollatzResearch.WordTrace tailWord_5072069 prefixEnd_5072069 2604409309769421240411485 := by
  unfold tailWord_5072069
  simp only [CollatzResearch.WordTrace]
  refine ⟨184993554261767728265387261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123329036174511818843591507 184993554261767728265387261)
  ·
    refine ⟨69372582848162898099520223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184993554261767728265387261 69372582848162898099520223)
    ·
      refine ⟨104058874272244347149280335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69372582848162898099520223 104058874272244347149280335)
      ·
        refine ⟨156088311408366520723920503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104058874272244347149280335 156088311408366520723920503)
        ·
          refine ⟨234132467112549781085880755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156088311408366520723920503 234132467112549781085880755)
          ·
            refine ⟨351198700668824671628821133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234132467112549781085880755 351198700668824671628821133)
            ·
              refine ⟨131699512750809251860807925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351198700668824671628821133 131699512750809251860807925)
              ·
                refine ⟨12346829320388367361950743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131699512750809251860807925 12346829320388367361950743)
                ·
                  refine ⟨18520243980582551042926115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12346829320388367361950743 18520243980582551042926115)
                  ·
                    refine ⟨27780365970873826564389173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18520243980582551042926115 27780365970873826564389173)
                    ·
                      refine ⟨2604409309769421240411485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27780365970873826564389173 2604409309769421240411485)
                      ·
                        rfl

theorem cell23_5072069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_5072069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072069 prefixEnd_5072069 := by exact prefixLift 5072069
  have htrace : WordTrace (prefixWord ++ tailWord_5072069) baseStart_5072069 baseEnd_5072069 := by
    simpa [prefixWord, tailWord_5072069, baseEnd_5072069] using wordTrace_append hprefix tailTrace_5072069
  have hstable : (prefixWord ++ tailWord_5072069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072069).length < 2 ^ (prefixWord ++ tailWord_5072069).sum := by decide
  have hdescent : baseEnd_5072069 < baseStart_5072069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072096 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4]
def baseStart_5072096 : Nat := 118140960795 + 5072096 * 2 ^ 59
def prefixEnd_5072096 : Nat := 4983230072969 + 3 ^ 40 * 5072096 * 2
def baseEnd_5072096 : Nat := 2604423173747092634773861

theorem tailTrace_5072096 : CollatzResearch.WordTrace tailWord_5072096 prefixEnd_5072096 2604423173747092634773861 := by
  unfold tailWord_5072096
  simp only [CollatzResearch.WordTrace]
  refine ⟨92497269516334955938310071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123329692688446607917746761 92497269516334955938310071)
  ·
    refine ⟨138745904274502433907465107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92497269516334955938310071 138745904274502433907465107)
    ·
      refine ⟨208118856411753650861197661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138745904274502433907465107 208118856411753650861197661)
      ·
        refine ⟨78044571154407619072949123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208118856411753650861197661 78044571154407619072949123)
        ·
          refine ⟨117066856731611428609423685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78044571154407619072949123 117066856731611428609423685)
          ·
            refine ⟨21950035637177142864266941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117066856731611428609423685 21950035637177142864266941)
            ·
              refine ⟨8231263363941428574100103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21950035637177142864266941 8231263363941428574100103)
              ·
                refine ⟨12346895045912142861150155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8231263363941428574100103 12346895045912142861150155)
                ·
                  refine ⟨18520342568868214291725233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12346895045912142861150155 18520342568868214291725233)
                  ·
                    refine ⟨13890256926651160718793925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18520342568868214291725233 13890256926651160718793925)
                    ·
                      refine ⟨2604423173747092634773861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13890256926651160718793925 2604423173747092634773861)
                      ·
                        rfl

theorem cell23_5072096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_5072096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072096 prefixEnd_5072096 := by exact prefixLift 5072096
  have htrace : WordTrace (prefixWord ++ tailWord_5072096) baseStart_5072096 baseEnd_5072096 := by
    simpa [prefixWord, tailWord_5072096, baseEnd_5072096] using wordTrace_append hprefix tailTrace_5072096
  have hstable : (prefixWord ++ tailWord_5072096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072096).length < 2 ^ (prefixWord ++ tailWord_5072096).sum := by decide
  have hdescent : baseEnd_5072096 < baseStart_5072096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072106 : List Nat := [3, 1, 3, 1, 1, 3, 4, 7]
def baseStart_5072106 : Nat := 118140960795 + 5072106 * 2 ^ 59
def prefixEnd_5072106 : Nat := 4983230072969 + 3 ^ 40 * 5072106 * 2
def baseEnd_5072106 : Nat := 96460307724208799838845

theorem tailTrace_5072106 : CollatzResearch.WordTrace tailWord_5072106 prefixEnd_5072106 96460307724208799838845 := by
  unfold tailWord_5072106
  simp only [CollatzResearch.WordTrace]
  refine ⟨46248725940658420896121043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123329935841755789056322781 46248725940658420896121043)
  ·
    refine ⟨69373088910987631344181565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46248725940658420896121043 69373088910987631344181565)
    ·
      refine ⟨26014908341620361754068087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69373088910987631344181565 26014908341620361754068087)
      ·
        refine ⟨39022362512430542631102131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26014908341620361754068087 39022362512430542631102131)
        ·
          refine ⟨58533543768645813946653197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39022362512430542631102131 58533543768645813946653197)
          ·
            refine ⟨21950078913242180229994949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58533543768645813946653197 21950078913242180229994949)
            ·
              refine ⟨4115639796232908793124053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21950078913242180229994949 4115639796232908793124053)
              ·
                refine ⟨96460307724208799838845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4115639796232908793124053 96460307724208799838845)
                ·
                  rfl

theorem cell23_5072106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_5072106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072106 prefixEnd_5072106 := by exact prefixLift 5072106
  have htrace : WordTrace (prefixWord ++ tailWord_5072106) baseStart_5072106 baseEnd_5072106 := by
    simpa [prefixWord, tailWord_5072106, baseEnd_5072106] using wordTrace_append hprefix tailTrace_5072106
  have hstable : (prefixWord ++ tailWord_5072106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072106).length < 2 ^ (prefixWord ++ tailWord_5072106).sum := by decide
  have hdescent : baseEnd_5072106 < baseStart_5072106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072133 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_5072133 : Nat := 118140960795 + 5072133 * 2 ^ 59
def prefixEnd_5072133 : Nat := 4983230072969 + 3 ^ 40 * 5072133 * 2
def baseEnd_5072133 : Nat := 2604442172531308990011191

theorem tailTrace_5072133 : CollatzResearch.WordTrace tailWord_5072133 prefixEnd_5072133 2604442172531308990011191 := by
  unfold tailWord_5072133
  simp only [CollatzResearch.WordTrace]
  refine ⟨184995888533535867195717053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123330592355690578130478035 184995888533535867195717053)
  ·
    refine ⟨69373458200075950198393895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184995888533535867195717053 69373458200075950198393895)
    ·
      refine ⟨104060187300113925297590843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69373458200075950198393895 104060187300113925297590843)
      ·
        refine ⟨156090280950170887946386265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104060187300113925297590843 156090280950170887946386265)
        ·
          refine ⟨117067710712628165959789699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156090280950170887946386265 117067710712628165959789699)
          ·
            refine ⟨175601566068942248939684549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117067710712628165959789699 175601566068942248939684549)
            ·
              refine ⟨32925293637926671676190853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175601566068942248939684549 32925293637926671676190853)
              ·
                refine ⟨6173492557111250939285785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32925293637926671676190853 6173492557111250939285785)
                ·
                  refine ⟨4630119417833438204464339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6173492557111250939285785 4630119417833438204464339)
                  ·
                    refine ⟨6945179126750157306696509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4630119417833438204464339 6945179126750157306696509)
                    ·
                      refine ⟨2604442172531308990011191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6945179126750157306696509 2604442172531308990011191)
                      ·
                        rfl

theorem cell23_5072133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_5072133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072133 prefixEnd_5072133 := by exact prefixLift 5072133
  have htrace : WordTrace (prefixWord ++ tailWord_5072133) baseStart_5072133 baseEnd_5072133 := by
    simpa [prefixWord, tailWord_5072133, baseEnd_5072133] using wordTrace_append hprefix tailTrace_5072133
  have hstable : (prefixWord ++ tailWord_5072133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072133).length < 2 ^ (prefixWord ++ tailWord_5072133).sum := by decide
  have hdescent : baseEnd_5072133 < baseStart_5072133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072149 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_5072149 : Nat := 118140960795 + 5072149 * 2 ^ 59
def prefixEnd_5072149 : Nat := 4983230072969 + 3 ^ 40 * 5072149 * 2
def baseEnd_5072149 : Nat := 868150129407260309137039

theorem tailTrace_5072149 : CollatzResearch.WordTrace tailWord_5072149 prefixEnd_5072149 868150129407260309137039 := by
  unfold tailWord_5072149
  simp only [CollatzResearch.WordTrace]
  refine ⟨184996472101477901928299501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123330981400985267952199667 184996472101477901928299501)
  ·
    refine ⟨69373677038054213223112313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184996472101477901928299501 69373677038054213223112313)
    ·
      refine ⟨52030257778540659917334235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69373677038054213223112313 52030257778540659917334235)
      ·
        refine ⟨78045386667810989876001353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52030257778540659917334235 78045386667810989876001353)
        ·
          refine ⟨58534040000858242407001015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78045386667810989876001353 58534040000858242407001015)
          ·
            refine ⟨87801060001287363610501523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58534040000858242407001015 87801060001287363610501523)
            ·
              refine ⟨131701590001931045415752285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87801060001287363610501523 131701590001931045415752285)
              ·
                refine ⟨49388096250724142030907107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131701590001931045415752285 49388096250724142030907107)
                ·
                  refine ⟨74082144376086213046360661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49388096250724142030907107 74082144376086213046360661)
                  ·
                    refine ⟨868150129407260309137039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74082144376086213046360661 868150129407260309137039)
                    ·
                      rfl

theorem cell23_5072149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_5072149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072149 prefixEnd_5072149 := by exact prefixLift 5072149
  have htrace : WordTrace (prefixWord ++ tailWord_5072149) baseStart_5072149 baseEnd_5072149 := by
    simpa [prefixWord, tailWord_5072149, baseEnd_5072149] using wordTrace_append hprefix tailTrace_5072149
  have hstable : (prefixWord ++ tailWord_5072149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072149).length < 2 ^ (prefixWord ++ tailWord_5072149).sum := by decide
  have hdescent : baseEnd_5072149 < baseStart_5072149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072160 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 3, 3, 2]
def baseStart_5072160 : Nat := 118140960795 + 5072160 * 2 ^ 59
def prefixEnd_5072160 : Nat := 4983230072969 + 3 ^ 40 * 5072160 * 2
def baseEnd_5072160 : Nat := 2604456036508980384373567

theorem tailTrace_5072160 : CollatzResearch.WordTrace tailWord_5072160 prefixEnd_5072160 2604456036508980384373567 := by
  unfold tailWord_5072160
  simp only [CollatzResearch.WordTrace]
  refine ⟨92498436652219025403474967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123331248869625367204633289 92498436652219025403474967)
  ·
    refine ⟨138747654978328538105212451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92498436652219025403474967 138747654978328538105212451)
    ·
      refine ⟨208121482467492807157818677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138747654978328538105212451 208121482467492807157818677)
      ·
        refine ⟨19511388981327450671045501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208121482467492807157818677 19511388981327450671045501)
        ·
          refine ⟨7316770867997794001642063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19511388981327450671045501 7316770867997794001642063)
          ·
            refine ⟨10975156301996691002463095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7316770867997794001642063 10975156301996691002463095)
            ·
              refine ⟨16462734452995036503694643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10975156301996691002463095 16462734452995036503694643)
              ·
                refine ⟨24694101679492554755541965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16462734452995036503694643 24694101679492554755541965)
                ·
                  refine ⟨9260288129809708033328237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24694101679492554755541965 9260288129809708033328237)
                  ·
                    refine ⟨3472608048678640512498089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9260288129809708033328237 3472608048678640512498089)
                    ·
                      refine ⟨2604456036508980384373567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472608048678640512498089 2604456036508980384373567)
                      ·
                        rfl

theorem cell23_5072160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_5072160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072160 prefixEnd_5072160 := by exact prefixLift 5072160
  have htrace : WordTrace (prefixWord ++ tailWord_5072160) baseStart_5072160 baseEnd_5072160 := by
    simpa [prefixWord, tailWord_5072160, baseEnd_5072160] using wordTrace_append hprefix tailTrace_5072160
  have hstable : (prefixWord ++ tailWord_5072160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072160).length < 2 ^ (prefixWord ++ tailWord_5072160).sum := by decide
  have hdescent : baseEnd_5072160 < baseStart_5072160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072177 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 1, 3, 2]
def baseStart_5072177 : Nat := 118140960795 + 5072177 * 2 ^ 59
def prefixEnd_5072177 : Nat := 4983230072969 + 3 ^ 40 * 5072177 * 2
def baseEnd_5072177 : Nat := 2604464765680106817860989

theorem tailTrace_5072177 : CollatzResearch.WordTrace tailWord_5072177 prefixEnd_5072177 2604464765680106817860989 := by
  unfold tailWord_5072177
  simp only [CollatzResearch.WordTrace]
  refine ⟨184997493345376462710318785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123331662230250975140212523 184997493345376462710318785)
  ·
    refine ⟨138748120009032347032739089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184997493345376462710318785 138748120009032347032739089)
    ·
      refine ⟨104061090006774260274554317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138748120009032347032739089 104061090006774260274554317)
      ·
        refine ⟨39022908752540347602957869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104061090006774260274554317 39022908752540347602957869)
        ·
          refine ⟨14633590782202630351109201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39022908752540347602957869 14633590782202630351109201)
          ·
            refine ⟨10975193086651972763331901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14633590782202630351109201 10975193086651972763331901)
            ·
              refine ⟨4115697407494489786249463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10975193086651972763331901 4115697407494489786249463)
              ·
                refine ⟨6173546111241734679374195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115697407494489786249463 6173546111241734679374195)
                ·
                  refine ⟨9260319166862602019061293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6173546111241734679374195 9260319166862602019061293)
                  ·
                    refine ⟨3472619687573475757147985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9260319166862602019061293 3472619687573475757147985)
                    ·
                      refine ⟨2604464765680106817860989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472619687573475757147985 2604464765680106817860989)
                      ·
                        rfl

theorem cell23_5072177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_5072177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072177 prefixEnd_5072177 := by exact prefixLift 5072177
  have htrace : WordTrace (prefixWord ++ tailWord_5072177) baseStart_5072177 baseEnd_5072177 := by
    simpa [prefixWord, tailWord_5072177, baseEnd_5072177] using wordTrace_append hprefix tailTrace_5072177
  have hstable : (prefixWord ++ tailWord_5072177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072177).length < 2 ^ (prefixWord ++ tailWord_5072177).sum := by decide
  have hdescent : baseEnd_5072177 < baseStart_5072177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072186 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_5072186 : Nat := 118140960795 + 5072186 * 2 ^ 59
def prefixEnd_5072186 : Nat := 4983230072969 + 3 ^ 40 * 5072186 * 2
def baseEnd_5072186 : Nat := 2604469387005997282648447

theorem tailTrace_5072186 : CollatzResearch.WordTrace tailWord_5072186 prefixEnd_5072186 2604469387005997282648447 := by
  unfold tailWord_5072186
  simp only [CollatzResearch.WordTrace]
  refine ⟨46249455400585964311849103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123331881068229238164930941 46249455400585964311849103)
  ·
    refine ⟨69374183100878946467773655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46249455400585964311849103 69374183100878946467773655)
    ·
      refine ⟨104061274651318419701660483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69374183100878946467773655 104061274651318419701660483)
      ·
        refine ⟨156091911976977629552490725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104061274651318419701660483 156091911976977629552490725)
        ·
          refine ⟨29267233495683305541092011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156091911976977629552490725 29267233495683305541092011)
          ·
            refine ⟨43900850243524958311638017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29267233495683305541092011 43900850243524958311638017)
            ·
              refine ⟨32925637682643718733728513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43900850243524958311638017 32925637682643718733728513)
              ·
                refine ⟨24694228261982789050296385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32925637682643718733728513 24694228261982789050296385)
                ·
                  refine ⟨18520671196487091787722289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24694228261982789050296385 18520671196487091787722289)
                  ·
                    refine ⟨13890503397365318840791717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18520671196487091787722289 13890503397365318840791717)
                    ·
                      refine ⟨2604469387005997282648447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13890503397365318840791717 2604469387005997282648447)
                      ·
                        rfl

theorem cell23_5072186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_5072186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072186 prefixEnd_5072186 := by exact prefixLift 5072186
  have htrace : WordTrace (prefixWord ++ tailWord_5072186) baseStart_5072186 baseEnd_5072186 := by
    simpa [prefixWord, tailWord_5072186, baseEnd_5072186] using wordTrace_append hprefix tailTrace_5072186
  have hstable : (prefixWord ++ tailWord_5072186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072186).length < 2 ^ (prefixWord ++ tailWord_5072186).sum := by decide
  have hdescent : baseEnd_5072186 < baseStart_5072186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072193 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5072193 : Nat := 118140960795 + 5072193 * 2 ^ 59
def prefixEnd_5072193 : Nat := 4983230072969 + 3 ^ 40 * 5072193 * 2
def baseEnd_5072193 : Nat := 2604472981370578755260915

theorem tailTrace_5072193 : CollatzResearch.WordTrace tailWord_5072193 prefixEnd_5072193 2604472981370578755260915 := by
  unfold tailWord_5072193
  simp only [CollatzResearch.WordTrace]
  refine ⟨184998076913318497442901233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123332051275545664961934155 184998076913318497442901233)
  ·
    refine ⟨138748557684988873082175925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184998076913318497442901233 138748557684988873082175925)
    ·
      refine ⟨13007677282967706851453993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138748557684988873082175925 13007677282967706851453993)
      ·
        refine ⟨9755757962225780138590495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13007677282967706851453993 9755757962225780138590495)
        ·
          refine ⟨14633636943338670207885743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9755757962225780138590495 14633636943338670207885743)
          ·
            refine ⟨21950455415008005311828615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14633636943338670207885743 21950455415008005311828615)
            ·
              refine ⟨32925683122512007967742923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21950455415008005311828615 32925683122512007967742923)
              ·
                refine ⟨49388524683768011951614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32925683122512007967742923 49388524683768011951614385)
                ·
                  refine ⟨37041393512826008963710789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49388524683768011951614385 37041393512826008963710789)
                  ·
                    refine ⟨6945261283654876680695773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37041393512826008963710789 6945261283654876680695773)
                    ·
                      refine ⟨2604472981370578755260915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6945261283654876680695773 2604472981370578755260915)
                      ·
                        rfl

theorem cell23_5072193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5072193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072193 prefixEnd_5072193 := by exact prefixLift 5072193
  have htrace : WordTrace (prefixWord ++ tailWord_5072193) baseStart_5072193 baseEnd_5072193 := by
    simpa [prefixWord, tailWord_5072193, baseEnd_5072193] using wordTrace_append hprefix tailTrace_5072193
  have hstable : (prefixWord ++ tailWord_5072193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072193).length < 2 ^ (prefixWord ++ tailWord_5072193).sum := by decide
  have hdescent : baseEnd_5072193 < baseStart_5072193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072306 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_5072306 : Nat := 118140960795 + 5072306 * 2 ^ 59
def prefixEnd_5072306 : Nat := 4983230072969 + 3 ^ 40 * 5072306 * 2
def baseEnd_5072306 : Nat := 2604531004684536813147895

theorem tailTrace_5072306 : CollatzResearch.WordTrace tailWord_5072306 prefixEnd_5072306 2604531004684536813147895 := by
  unfold tailWord_5072306
  simp only [CollatzResearch.WordTrace]
  refine ⟨46250549590477279435441193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123334798907939411827843181 46250549590477279435441193)
  ·
    refine ⟨34687912192857959576580895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46250549590477279435441193 34687912192857959576580895)
    ·
      refine ⟨52031868289286939364871343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34687912192857959576580895 52031868289286939364871343)
      ·
        refine ⟨78047802433930409047307015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52031868289286939364871343 78047802433930409047307015)
        ·
          refine ⟨117071703650895613570960523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78047802433930409047307015 117071703650895613570960523)
          ·
            refine ⟨175607555476343420356440785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117071703650895613570960523 175607555476343420356440785)
            ·
              refine ⟨131705666607257565267330589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175607555476343420356440785 131705666607257565267330589)
              ·
                refine ⟨49389624977721586975248971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131705666607257565267330589 49389624977721586975248971)
                ·
                  refine ⟨74084437466582380462873457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49389624977721586975248971 74084437466582380462873457)
                  ·
                    refine ⟨55563328099936785347155093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74084437466582380462873457 55563328099936785347155093)
                    ·
                      refine ⟨2604531004684536813147895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55563328099936785347155093 2604531004684536813147895)
                      ·
                        rfl

theorem cell23_5072306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_5072306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072306 prefixEnd_5072306 := by exact prefixLift 5072306
  have htrace : WordTrace (prefixWord ++ tailWord_5072306) baseStart_5072306 baseEnd_5072306 := by
    simpa [prefixWord, tailWord_5072306, baseEnd_5072306] using wordTrace_append hprefix tailTrace_5072306
  have hstable : (prefixWord ++ tailWord_5072306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072306).length < 2 ^ (prefixWord ++ tailWord_5072306).sum := by decide
  have hdescent : baseEnd_5072306 < baseStart_5072306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072323 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 3, 5, 2]
def baseStart_5072323 : Nat := 118140960795 + 5072323 * 2 ^ 59
def prefixEnd_5072323 : Nat := 4983230072969 + 3 ^ 40 * 5072323 * 2
def baseEnd_5072323 : Nat := 2604539733855663246635317

theorem tailTrace_5072323 : CollatzResearch.WordTrace tailWord_5072323 prefixEnd_5072323 2604539733855663246635317 := by
  unfold tailWord_5072323
  simp only [CollatzResearch.WordTrace]
  refine ⟨185002818402847529645133623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123335212268565019763422415 185002818402847529645133623)
  ·
    refine ⟨277504227604271294467700435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185002818402847529645133623 277504227604271294467700435)
    ·
      refine ⟨416256341406406941701550653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277504227604271294467700435 416256341406406941701550653)
      ·
        refine ⟨156096128027402603138081495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416256341406406941701550653 156096128027402603138081495)
        ·
          refine ⟨234144192041103904707122243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156096128027402603138081495 234144192041103904707122243)
          ·
            refine ⟨351216288061655857060683365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234144192041103904707122243 351216288061655857060683365)
            ·
              refine ⟨65853054011560473198878131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 351216288061655857060683365 65853054011560473198878131)
              ·
                refine ⟨98779581017340709798317197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65853054011560473198878131 98779581017340709798317197)
                ·
                  refine ⟨37042342881502766174368949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98779581017340709798317197 37042342881502766174368949)
                  ·
                    refine ⟨3472719645140884328847089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37042342881502766174368949 3472719645140884328847089)
                    ·
                      refine ⟨2604539733855663246635317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472719645140884328847089 2604539733855663246635317)
                      ·
                        rfl

theorem cell23_5072323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_5072323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072323 prefixEnd_5072323 := by exact prefixLift 5072323
  have htrace : WordTrace (prefixWord ++ tailWord_5072323) baseStart_5072323 baseEnd_5072323 := by
    simpa [prefixWord, tailWord_5072323, baseEnd_5072323] using wordTrace_append hprefix tailTrace_5072323
  have hstable : (prefixWord ++ tailWord_5072323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072323).length < 2 ^ (prefixWord ++ tailWord_5072323).sum := by decide
  have hdescent : baseEnd_5072323 < baseStart_5072323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072336 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_5072336 : Nat := 118140960795 + 5072336 * 2 ^ 59
def prefixEnd_5072336 : Nat := 4983230072969 + 3 ^ 40 * 5072336 * 2
def baseEnd_5072336 : Nat := 2604546409104171695772757

theorem tailTrace_5072336 : CollatzResearch.WordTrace tailWord_5072336 prefixEnd_5072336 2604546409104171695772757 := by
  unfold tailWord_5072336
  simp only [CollatzResearch.WordTrace]
  refine ⟨92501646275900216432678431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123335528367866955243571241 92501646275900216432678431)
  ·
    refine ⟨138752469413850324649017647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92501646275900216432678431 138752469413850324649017647)
    ·
      refine ⟨208128704120775486973526471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138752469413850324649017647 208128704120775486973526471)
      ·
        refine ⟨312193056181163230460289707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208128704120775486973526471 312193056181163230460289707)
        ·
          refine ⟨468289584271744845690434561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312193056181163230460289707 468289584271744845690434561)
          ·
            refine ⟨351217188203808634267825921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468289584271744845690434561 351217188203808634267825921)
            ·
              refine ⟨263412891152856475700869441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351217188203808634267825921 263412891152856475700869441)
              ·
                refine ⟨197559668364642356775652081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263412891152856475700869441 197559668364642356775652081)
                ·
                  refine ⟨148169751273481767581739061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197559668364642356775652081 148169751273481767581739061)
                  ·
                    refine ⟨13890914181888915710788037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148169751273481767581739061 13890914181888915710788037)
                    ·
                      refine ⟨2604546409104171695772757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13890914181888915710788037 2604546409104171695772757)
                      ·
                        rfl

theorem cell23_5072336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_5072336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072336 prefixEnd_5072336 := by exact prefixLift 5072336
  have htrace : WordTrace (prefixWord ++ tailWord_5072336) baseStart_5072336 baseEnd_5072336 := by
    simpa [prefixWord, tailWord_5072336, baseEnd_5072336] using wordTrace_append hprefix tailTrace_5072336
  have hstable : (prefixWord ++ tailWord_5072336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072336).length < 2 ^ (prefixWord ++ tailWord_5072336).sum := by decide
  have hdescent : baseEnd_5072336 < baseStart_5072336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072357 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 2, 3, 2]
def baseStart_5072357 : Nat := 118140960795 + 5072357 * 2 ^ 59
def prefixEnd_5072357 : Nat := 4983230072969 + 3 ^ 40 * 5072357 * 2
def baseEnd_5072357 : Nat := 2604557192197916113610161

theorem tailTrace_5072357 : CollatzResearch.WordTrace tailWord_5072357 prefixEnd_5072357 2604557192197916113610161 := by
  unfold tailWord_5072357
  simp only [CollatzResearch.WordTrace]
  refine ⟨185004058484724353451871325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123336038989816235634580883 185004058484724353451871325)
  ·
    refine ⟨69376521931771632544451747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185004058484724353451871325 69376521931771632544451747)
    ·
      refine ⟨104064782897657448816677621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69376521931771632544451747 104064782897657448816677621)
      ·
        refine ⟨9756073396655385826563527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104064782897657448816677621 9756073396655385826563527)
        ·
          refine ⟨14634110094983078739845291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9756073396655385826563527 14634110094983078739845291)
          ·
            refine ⟨21951165142474618109767937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14634110094983078739845291 21951165142474618109767937)
            ·
              refine ⟨16463373856855963582325953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21951165142474618109767937 16463373856855963582325953)
              ·
                refine ⟨12347530392641972686744465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16463373856855963582325953 12347530392641972686744465)
                ·
                  refine ⟨9260647794481479515058349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12347530392641972686744465 9260647794481479515058349)
                  ·
                    refine ⟨3472742922930554818146881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9260647794481479515058349 3472742922930554818146881)
                    ·
                      refine ⟨2604557192197916113610161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472742922930554818146881 2604557192197916113610161)
                      ·
                        rfl

theorem cell23_5072357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_5072357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072357 prefixEnd_5072357 := by exact prefixLift 5072357
  have htrace : WordTrace (prefixWord ++ tailWord_5072357) baseStart_5072357 baseEnd_5072357 := by
    simpa [prefixWord, tailWord_5072357, baseEnd_5072357] using wordTrace_append hprefix tailTrace_5072357
  have hstable : (prefixWord ++ tailWord_5072357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072357).length < 2 ^ (prefixWord ++ tailWord_5072357).sum := by decide
  have hdescent : baseEnd_5072357 < baseStart_5072357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072370 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5072370 : Nat := 118140960795 + 5072370 * 2 ^ 59
def prefixEnd_5072370 : Nat := 4983230072969 + 3 ^ 40 * 5072370 * 2
def baseEnd_5072370 : Nat := 2604563867446424562747601

theorem tailTrace_5072370 : CollatzResearch.WordTrace tailWord_5072370 prefixEnd_5072370 2604563867446424562747601 := by
  unfold tailWord_5072370
  simp only [CollatzResearch.WordTrace]
  refine ⟨46251133158419314168023641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123336355089118171114729709 46251133158419314168023641)
  ·
    refine ⟨34688349868814485626017731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46251133158419314168023641 34688349868814485626017731)
    ·
      refine ⟨52032524803221728439026597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34688349868814485626017731 52032524803221728439026597)
      ·
        refine ⟨9756098400604074082317487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52032524803221728439026597 9756098400604074082317487)
        ·
          refine ⟨14634147600906111123476231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9756098400604074082317487 14634147600906111123476231)
          ·
            refine ⟨21951221401359166685214347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14634147600906111123476231 21951221401359166685214347)
            ·
              refine ⟨32926832102038750027821521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21951221401359166685214347 32926832102038750027821521)
              ·
                refine ⟨24695124076529062520866141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32926832102038750027821521 24695124076529062520866141)
                ·
                  refine ⟨9260671528698398445324803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24695124076529062520866141 9260671528698398445324803)
                  ·
                    refine ⟨13891007293047597667987205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9260671528698398445324803 13891007293047597667987205)
                    ·
                      refine ⟨2604563867446424562747601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13891007293047597667987205 2604563867446424562747601)
                      ·
                        rfl

theorem cell23_5072370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5072370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072370 prefixEnd_5072370 := by exact prefixLift 5072370
  have htrace : WordTrace (prefixWord ++ tailWord_5072370) baseStart_5072370 baseEnd_5072370 := by
    simpa [prefixWord, tailWord_5072370, baseEnd_5072370] using wordTrace_append hprefix tailTrace_5072370
  have hstable : (prefixWord ++ tailWord_5072370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072370).length < 2 ^ (prefixWord ++ tailWord_5072370).sum := by decide
  have hdescent : baseEnd_5072370 < baseStart_5072370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072380 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_5072380 : Nat := 118140960795 + 5072380 * 2 ^ 59
def prefixEnd_5072380 : Nat := 4983230072969 + 3 ^ 40 * 5072380 * 2
def baseEnd_5072380 : Nat := 868189667417656507874185

theorem tailTrace_5072380 : CollatzResearch.WordTrace tailWord_5072380 prefixEnd_5072380 868189667417656507874185 := by
  unfold tailWord_5072380
  simp only [CollatzResearch.WordTrace]
  refine ⟨92502448681820514189979297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123336598242427352253305729 92502448681820514189979297)
  ·
    refine ⟨69376836511365385642484473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92502448681820514189979297 69376836511365385642484473)
    ·
      refine ⟨52032627383524039231863355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69376836511365385642484473 52032627383524039231863355)
      ·
        refine ⟨78048941075286058847795033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52032627383524039231863355 78048941075286058847795033)
        ·
          refine ⟨58536705806464544135846275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78048941075286058847795033 58536705806464544135846275)
          ·
            refine ⟨87805058709696816203769413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58536705806464544135846275 87805058709696816203769413)
            ·
              refine ⟨16463448508068153038206765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87805058709696816203769413 16463448508068153038206765)
              ·
                refine ⟨6173793190525557389327537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16463448508068153038206765 6173793190525557389327537)
                ·
                  refine ⟨4630344892894168041995653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6173793190525557389327537 4630344892894168041995653)
                  ·
                    refine ⟨868189667417656507874185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630344892894168041995653 868189667417656507874185)
                    ·
                      rfl

theorem cell23_5072380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_5072380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072380 prefixEnd_5072380 := by exact prefixLift 5072380
  have htrace : WordTrace (prefixWord ++ tailWord_5072380) baseStart_5072380 baseEnd_5072380 := by
    simpa [prefixWord, tailWord_5072380, baseEnd_5072380] using wordTrace_append hprefix tailTrace_5072380
  have hstable : (prefixWord ++ tailWord_5072380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072380).length < 2 ^ (prefixWord ++ tailWord_5072380).sum := by decide
  have hdescent : baseEnd_5072380 < baseStart_5072380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072393 : List Nat := [1, 2, 1, 1, 3, 1, 7, 7]
def baseStart_5072393 : Nat := 118140960795 + 5072393 * 2 ^ 59
def prefixEnd_5072393 : Nat := 4983230072969 + 3 ^ 40 * 5072393 * 2
def baseEnd_5072393 : Nat := 96465765833388073065185

theorem tailTrace_5072393 : CollatzResearch.WordTrace tailWord_5072393 prefixEnd_5072393 96465765833388073065185 := by
  unfold tailWord_5072393
  simp only [CollatzResearch.WordTrace]
  refine ⟨185005371512593931600181833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123336914341729287733454555 185005371512593931600181833)
  ·
    refine ⟨138754028634445448700136375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185005371512593931600181833 138754028634445448700136375)
    ·
      refine ⟨208131042951668173050204563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138754028634445448700136375 208131042951668173050204563)
      ·
        refine ⟨312196564427502259575306845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208131042951668173050204563 312196564427502259575306845)
        ·
          refine ⟨117073711660313347340740067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312196564427502259575306845 117073711660313347340740067)
          ·
            refine ⟨175610567490470021011110101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117073711660313347340740067 175610567490470021011110101)
            ·
              refine ⟨4115872675557891117447893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 175610567490470021011110101 4115872675557891117447893)
              ·
                refine ⟨96465765833388073065185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4115872675557891117447893 96465765833388073065185)
                ·
                  rfl

theorem cell23_5072393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 7].length) (baseStart_5072393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072393 prefixEnd_5072393 := by exact prefixLift 5072393
  have htrace : WordTrace (prefixWord ++ tailWord_5072393) baseStart_5072393 baseEnd_5072393 := by
    simpa [prefixWord, tailWord_5072393, baseEnd_5072393] using wordTrace_append hprefix tailTrace_5072393
  have hstable : (prefixWord ++ tailWord_5072393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072393).length < 2 ^ (prefixWord ++ tailWord_5072393).sum := by decide
  have hdescent : baseEnd_5072393 < baseStart_5072393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072404 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5072404 : Nat := 118140960795 + 5072404 * 2 ^ 59
def prefixEnd_5072404 : Nat := 4983230072969 + 3 ^ 40 * 5072404 * 2
def baseEnd_5072404 : Nat := 2604581325788677429722445

theorem tailTrace_5072404 : CollatzResearch.WordTrace tailWord_5072404 prefixEnd_5072404 2604581325788677429722445 := by
  unfold tailWord_5072404
  simp only [CollatzResearch.WordTrace]
  refine ⟨92502886357777040239416133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123337181810369386985888177 92502886357777040239416133)
  ·
    refine ⟨17344291192083195044890525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92502886357777040239416133 17344291192083195044890525)
    ·
      refine ⟨6504109197031198141833947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17344291192083195044890525 6504109197031198141833947)
      ·
        refine ⟨9756163795546797212750921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504109197031198141833947 9756163795546797212750921)
        ·
          refine ⟨7317122846660097909563191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9756163795546797212750921 7317122846660097909563191)
          ·
            refine ⟨10975684269990146864344787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317122846660097909563191 10975684269990146864344787)
            ·
              refine ⟨16463526404985220296517181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10975684269990146864344787 16463526404985220296517181)
              ·
                refine ⟨6173822401869457611193943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16463526404985220296517181 6173822401869457611193943)
                ·
                  refine ⟨9260733602804186416790915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6173822401869457611193943 9260733602804186416790915)
                  ·
                    refine ⟨13891100404206279625186373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9260733602804186416790915 13891100404206279625186373)
                    ·
                      refine ⟨2604581325788677429722445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13891100404206279625186373 2604581325788677429722445)
                      ·
                        rfl

theorem cell23_5072404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5072404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072404 prefixEnd_5072404 := by exact prefixLift 5072404
  have htrace : WordTrace (prefixWord ++ tailWord_5072404) baseStart_5072404 baseEnd_5072404 := by
    simpa [prefixWord, tailWord_5072404, baseEnd_5072404] using wordTrace_append hprefix tailTrace_5072404
  have hstable : (prefixWord ++ tailWord_5072404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072404).length < 2 ^ (prefixWord ++ tailWord_5072404).sum := by decide
  have hdescent : baseEnd_5072404 < baseStart_5072404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072437 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_5072437 : Nat := 118140960795 + 5072437 * 2 ^ 59
def prefixEnd_5072437 : Nat := 4983230072969 + 3 ^ 40 * 5072437 * 2
def baseEnd_5072437 : Nat := 2604598270650275800609793

theorem tailTrace_5072437 : CollatzResearch.WordTrace tailWord_5072437 prefixEnd_5072437 2604598270650275800609793 := by
  unfold tailWord_5072437
  simp only [CollatzResearch.WordTrace]
  refine ⟨185006976324434527114783565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123337984216289684743189043 185006976324434527114783565)
  ·
    refine ⟨69377616121662947668043837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185006976324434527114783565 69377616121662947668043837)
    ·
      refine ⟨26016606045623605375516439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69377616121662947668043837 26016606045623605375516439)
      ·
        refine ⟨39024909068435408063274659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26016606045623605375516439 39024909068435408063274659)
        ·
          refine ⟨58537363602653112094911989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39024909068435408063274659 58537363602653112094911989)
          ·
            refine ⟨5487877837748729258897999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58537363602653112094911989 5487877837748729258897999)
            ·
              refine ⟨8231816756623093888346999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5487877837748729258897999 8231816756623093888346999)
              ·
                refine ⟨12347725134934640832520499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8231816756623093888346999 12347725134934640832520499)
                ·
                  refine ⟨18521587702401961248780749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12347725134934640832520499 18521587702401961248780749)
                  ·
                    refine ⟨6945595388400735468292781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18521587702401961248780749 6945595388400735468292781)
                    ·
                      refine ⟨2604598270650275800609793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6945595388400735468292781 2604598270650275800609793)
                      ·
                        rfl

theorem cell23_5072437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_5072437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072437 prefixEnd_5072437 := by exact prefixLift 5072437
  have htrace : WordTrace (prefixWord ++ tailWord_5072437) baseStart_5072437 baseEnd_5072437 := by
    simpa [prefixWord, tailWord_5072437, baseEnd_5072437] using wordTrace_append hprefix tailTrace_5072437
  have hstable : (prefixWord ++ tailWord_5072437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072437).length < 2 ^ (prefixWord ++ tailWord_5072437).sum := by decide
  have hdescent : baseEnd_5072437 < baseStart_5072437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072447 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 1, 3, 2]
def baseStart_5072447 : Nat := 118140960795 + 5072447 * 2 ^ 59
def prefixEnd_5072447 : Nat := 4983230072969 + 3 ^ 40 * 5072447 * 2
def baseEnd_5072447 : Nat := 2604603405456820761484747

theorem tailTrace_5072447 : CollatzResearch.WordTrace tailWord_5072447 prefixEnd_5072447 2604603405456820761484747 := by
  unfold tailWord_5072447
  simp only [CollatzResearch.WordTrace]
  refine ⟨185007341054398298822647595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123338227369598865881765063 185007341054398298822647595)
  ·
    refine ⟨277511011581597448233971393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185007341054398298822647595 277511011581597448233971393)
    ·
      refine ⟨208133258686198086175478545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277511011581597448233971393 208133258686198086175478545)
      ·
        refine ⟨156099944014648564631608909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208133258686198086175478545 156099944014648564631608909)
        ·
          refine ⟨58537479005493211736853341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156099944014648564631608909 58537479005493211736853341)
          ·
            refine ⟨21951554627059954401320003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58537479005493211736853341 21951554627059954401320003)
            ·
              refine ⟨32927331940589931601980005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21951554627059954401320003 32927331940589931601980005)
              ·
                refine ⟨6173874738860612175371251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32927331940589931601980005 6173874738860612175371251)
                ·
                  refine ⟨9260812108290918263056877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6173874738860612175371251 9260812108290918263056877)
                  ·
                    refine ⟨3472804540609094348646329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9260812108290918263056877 3472804540609094348646329)
                    ·
                      refine ⟨2604603405456820761484747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472804540609094348646329 2604603405456820761484747)
                      ·
                        rfl

theorem cell23_5072447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_5072447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072447 prefixEnd_5072447 := by exact prefixLift 5072447
  have htrace : WordTrace (prefixWord ++ tailWord_5072447) baseStart_5072447 baseEnd_5072447 := by
    simpa [prefixWord, tailWord_5072447, baseEnd_5072447] using wordTrace_append hprefix tailTrace_5072447
  have hstable : (prefixWord ++ tailWord_5072447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072447).length < 2 ^ (prefixWord ++ tailWord_5072447).sum := by decide
  have hdescent : baseEnd_5072447 < baseStart_5072447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072463 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 3]
def baseStart_5072463 : Nat := 118140960795 + 5072463 * 2 ^ 59
def prefixEnd_5072463 : Nat := 4983230072969 + 3 ^ 40 * 5072463 * 2
def baseEnd_5072463 : Nat := 2604611621147292698884673

theorem tailTrace_5072463 : CollatzResearch.WordTrace tailWord_5072463 prefixEnd_5072463 2604611621147292698884673 := by
  unfold tailWord_5072463
  simp only [CollatzResearch.WordTrace]
  refine ⟨185007924622340333555230043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123338616414893555703486695 185007924622340333555230043)
  ·
    refine ⟨277511886933510500332845065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185007924622340333555230043 277511886933510500332845065)
    ·
      refine ⟨208133915200132875249633799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277511886933510500332845065 208133915200132875249633799)
      ·
        refine ⟨312200872800199312874450699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208133915200132875249633799 312200872800199312874450699)
        ·
          refine ⟨468301309200298969311676049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312200872800199312874450699 468301309200298969311676049)
          ·
            refine ⟨351225981900224226983757037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468301309200298969311676049 351225981900224226983757037)
            ·
              refine ⟨131709743212584085118908889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351225981900224226983757037 131709743212584085118908889)
              ·
                refine ⟨98782307409438063839181667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131709743212584085118908889 98782307409438063839181667)
                ·
                  refine ⟨148173461114157095758772501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98782307409438063839181667 148173461114157095758772501)
                  ·
                    refine ⟨6945630989726113863692461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148173461114157095758772501 6945630989726113863692461)
                    ·
                      refine ⟨2604611621147292698884673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6945630989726113863692461 2604611621147292698884673)
                      ·
                        rfl

theorem cell23_5072463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_5072463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072463 prefixEnd_5072463 := by exact prefixLift 5072463
  have htrace : WordTrace (prefixWord ++ tailWord_5072463) baseStart_5072463 baseEnd_5072463 := by
    simpa [prefixWord, tailWord_5072463, baseEnd_5072463] using wordTrace_append hprefix tailTrace_5072463
  have hstable : (prefixWord ++ tailWord_5072463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072463).length < 2 ^ (prefixWord ++ tailWord_5072463).sum := by decide
  have hdescent : baseEnd_5072463 < baseStart_5072463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072473 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_5072473 : Nat := 118140960795 + 5072473 * 2 ^ 59
def prefixEnd_5072473 : Nat := 4983230072969 + 3 ^ 40 * 5072473 * 2
def baseEnd_5072473 : Nat := 2604616755953837659759627

theorem tailTrace_5072473 : CollatzResearch.WordTrace tailWord_5072473 prefixEnd_5072473 2604616755953837659759627 := by
  unfold tailWord_5072473
  simp only [CollatzResearch.WordTrace]
  refine ⟨185008289352304105263094073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123338859568202736842062715 185008289352304105263094073)
  ·
    refine ⟨138756217014228078947320555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185008289352304105263094073 138756217014228078947320555)
    ·
      refine ⟨208134325521342118420980833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138756217014228078947320555 208134325521342118420980833)
      ·
        refine ⟨156100744141006588815735625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208134325521342118420980833 156100744141006588815735625)
        ·
          refine ⟨117075558105754941611801719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156100744141006588815735625 117075558105754941611801719)
          ·
            refine ⟨175613337158632412417702579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117075558105754941611801719 175613337158632412417702579)
            ·
              refine ⟨263420005737948618626553869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175613337158632412417702579 263420005737948618626553869)
              ·
                refine ⟨98782502151730731984957701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263420005737948618626553869 98782502151730731984957701)
                ·
                  refine ⟨18521719153449512247179569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98782502151730731984957701 18521719153449512247179569)
                  ·
                    refine ⟨13891289365087134185384677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18521719153449512247179569 13891289365087134185384677)
                    ·
                      refine ⟨2604616755953837659759627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13891289365087134185384677 2604616755953837659759627)
                      ·
                        rfl

theorem cell23_5072473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_5072473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072473 prefixEnd_5072473 := by exact prefixLift 5072473
  have htrace : WordTrace (prefixWord ++ tailWord_5072473) baseStart_5072473 baseEnd_5072473 := by
    simpa [prefixWord, tailWord_5072473, baseEnd_5072473] using wordTrace_append hprefix tailTrace_5072473
  have hstable : (prefixWord ++ tailWord_5072473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072473).length < 2 ^ (prefixWord ++ tailWord_5072473).sum := by decide
  have hdescent : baseEnd_5072473 < baseStart_5072473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072523 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5]
def baseStart_5072523 : Nat := 118140960795 + 5072523 * 2 ^ 59
def prefixEnd_5072523 : Nat := 4983230072969 + 3 ^ 40 * 5072523 * 2
def baseEnd_5072523 : Nat := 2604642429986562464134397

theorem tailTrace_5072523 : CollatzResearch.WordTrace tailWord_5072523 prefixEnd_5072523 2604642429986562464134397 := by
  unfold tailWord_5072523
  simp only [CollatzResearch.WordTrace]
  refine ⟨185010113002122963802414223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123340075334748642534942815 185010113002122963802414223)
  ·
    refine ⟨277515169503184445703621335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185010113002122963802414223 277515169503184445703621335)
    ·
      refine ⟨416272754254776668555432003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277515169503184445703621335 416272754254776668555432003)
      ·
        refine ⟨624409131382165002833148005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416272754254776668555432003 624409131382165002833148005)
        ·
          refine ⟨117076712134155938031215251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 624409131382165002833148005 117076712134155938031215251)
          ·
            refine ⟨175615068201233907046822877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117076712134155938031215251 175615068201233907046822877)
            ·
              refine ⟨65855650575462715142558579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175615068201233907046822877 65855650575462715142558579)
              ·
                refine ⟨98783475863194072713837869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65855650575462715142558579 98783475863194072713837869)
                ·
                  refine ⟨37043803448697777267689201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98783475863194072713837869 37043803448697777267689201)
                  ·
                    refine ⟨27782852586523332950766901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37043803448697777267689201 27782852586523332950766901)
                    ·
                      refine ⟨2604642429986562464134397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27782852586523332950766901 2604642429986562464134397)
                      ·
                        rfl

theorem cell23_5072523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_5072523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072523 prefixEnd_5072523 := by exact prefixLift 5072523
  have htrace : WordTrace (prefixWord ++ tailWord_5072523) baseStart_5072523 baseEnd_5072523 := by
    simpa [prefixWord, tailWord_5072523, baseEnd_5072523] using wordTrace_append hprefix tailTrace_5072523
  have hstable : (prefixWord ++ tailWord_5072523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072523).length < 2 ^ (prefixWord ++ tailWord_5072523).sum := by decide
  have hdescent : baseEnd_5072523 < baseStart_5072523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072553 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_5072553 : Nat := 118140960795 + 5072553 * 2 ^ 59
def prefixEnd_5072553 : Nat := 4983230072969 + 3 ^ 40 * 5072553 * 2
def baseEnd_5072553 : Nat := 2604657834406197346759259

theorem tailTrace_5072553 : CollatzResearch.WordTrace tailWord_5072553 prefixEnd_5072553 2604657834406197346759259 := by
  unfold tailWord_5072553
  simp only [CollatzResearch.WordTrace]
  refine ⟨185011207192014278926006313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123340804794676185950670875 185011207192014278926006313)
  ·
    refine ⟨138758405394010709194504735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185011207192014278926006313 138758405394010709194504735)
    ·
      refine ⟨208137608091016063791757103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138758405394010709194504735 208137608091016063791757103)
      ·
        refine ⟨312206412136524095687635655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208137608091016063791757103 312206412136524095687635655)
        ·
          refine ⟨468309618204786143531453483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312206412136524095687635655 468309618204786143531453483)
          ·
            refine ⟨702464427307179215297180225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468309618204786143531453483 702464427307179215297180225)
            ·
              refine ⟨526848320480384411472885169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702464427307179215297180225 526848320480384411472885169)
              ·
                refine ⟨395136240360288308604663877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526848320480384411472885169 395136240360288308604663877)
                ·
                  refine ⟨74088045067554057863374477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395136240360288308604663877 74088045067554057863374477)
                  ·
                    refine ⟨27783016900332771698765429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74088045067554057863374477 27783016900332771698765429)
                    ·
                      refine ⟨2604657834406197346759259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27783016900332771698765429 2604657834406197346759259)
                      ·
                        rfl

theorem cell23_5072553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_5072553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072553 prefixEnd_5072553 := by exact prefixLift 5072553
  have htrace : WordTrace (prefixWord ++ tailWord_5072553) baseStart_5072553 baseEnd_5072553 := by
    simpa [prefixWord, tailWord_5072553, baseEnd_5072553] using wordTrace_append hprefix tailTrace_5072553
  have hstable : (prefixWord ++ tailWord_5072553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072553).length < 2 ^ (prefixWord ++ tailWord_5072553).sum := by decide
  have hdescent : baseEnd_5072553 < baseStart_5072553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072560 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 5, 4]
def baseStart_5072560 : Nat := 118140960795 + 5072560 * 2 ^ 59
def prefixEnd_5072560 : Nat := 4983230072969 + 3 ^ 40 * 5072560 * 2
def baseEnd_5072560 : Nat := 868220476256926273123909

theorem tailTrace_5072560 : CollatzResearch.WordTrace tailWord_5072560 prefixEnd_5072560 868220476256926273123909 := by
  unfold tailWord_5072560
  simp only [CollatzResearch.WordTrace]
  refine ⟨92505731251494459560755567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123340975001992612747674089 92505731251494459560755567)
  ·
    refine ⟨138758596877241689341133351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92505731251494459560755567 138758596877241689341133351)
    ·
      refine ⟨208137895315862534011700027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138758596877241689341133351 208137895315862534011700027)
      ·
        refine ⟨312206842973793801017550041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208137895315862534011700027 312206842973793801017550041)
        ·
          refine ⟨234155132230345350763162531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312206842973793801017550041 234155132230345350763162531)
          ·
            refine ⟨351232698345518026144743797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234155132230345350763162531 351232698345518026144743797)
            ·
              refine ⟨32928065469892314951069731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 351232698345518026144743797 32928065469892314951069731)
              ·
                refine ⟨49392098204838472426604597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32928065469892314951069731 49392098204838472426604597)
                ·
                  refine ⟨4630509206703606789994181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49392098204838472426604597 4630509206703606789994181)
                  ·
                    refine ⟨868220476256926273123909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630509206703606789994181 868220476256926273123909)
                    ·
                      rfl

theorem cell23_5072560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_5072560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072560 prefixEnd_5072560 := by exact prefixLift 5072560
  have htrace : WordTrace (prefixWord ++ tailWord_5072560) baseStart_5072560 baseEnd_5072560 := by
    simpa [prefixWord, tailWord_5072560, baseEnd_5072560] using wordTrace_append hprefix tailTrace_5072560
  have hstable : (prefixWord ++ tailWord_5072560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072560).length < 2 ^ (prefixWord ++ tailWord_5072560).sum := by decide
  have hdescent : baseEnd_5072560 < baseStart_5072560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072567 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_5072567 : Nat := 118140960795 + 5072567 * 2 ^ 59
def prefixEnd_5072567 : Nat := 4983230072969 + 3 ^ 40 * 5072567 * 2
def baseEnd_5072567 : Nat := 2604665023135360291984195

theorem tailTrace_5072567 : CollatzResearch.WordTrace tailWord_5072567 prefixEnd_5072567 2604665023135360291984195 := by
  unfold tailWord_5072567
  simp only [CollatzResearch.WordTrace]
  refine ⟨185011717813963559317015955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123341145209309039544677303 185011717813963559317015955)
  ·
    refine ⟨277517576720945338975523933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185011717813963559317015955 277517576720945338975523933)
    ·
      refine ⟨104069091270354502115821475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277517576720945338975523933 104069091270354502115821475)
      ·
        refine ⟨156103636905531753173732213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104069091270354502115821475 156103636905531753173732213)
        ·
          refine ⟨14634715959893601860037395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156103636905531753173732213 14634715959893601860037395)
          ·
            refine ⟨21952073939840402790056093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14634715959893601860037395 21952073939840402790056093)
            ·
              refine ⟨8232027727440151046271035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21952073939840402790056093 8232027727440151046271035)
              ·
                refine ⟨12348041591160226569406553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8232027727440151046271035 12348041591160226569406553)
                ·
                  refine ⟨9261031193370169927054915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12348041591160226569406553 9261031193370169927054915)
                  ·
                    refine ⟨13891546790055254890582373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9261031193370169927054915 13891546790055254890582373)
                    ·
                      refine ⟨2604665023135360291984195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13891546790055254890582373 2604665023135360291984195)
                      ·
                        rfl

theorem cell23_5072567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_5072567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072567 prefixEnd_5072567 := by exact prefixLift 5072567
  have htrace : WordTrace (prefixWord ++ tailWord_5072567) baseStart_5072567 baseEnd_5072567 := by
    simpa [prefixWord, tailWord_5072567, baseEnd_5072567] using wordTrace_append hprefix tailTrace_5072567
  have hstable : (prefixWord ++ tailWord_5072567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072567).length < 2 ^ (prefixWord ++ tailWord_5072567).sum := by decide
  have hdescent : baseEnd_5072567 < baseStart_5072567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072580 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5072580 : Nat := 118140960795 + 5072580 * 2 ^ 59
def prefixEnd_5072580 : Nat := 4983230072969 + 3 ^ 40 * 5072580 * 2
def baseEnd_5072580 : Nat := 2604671698383868741121635

theorem tailTrace_5072580 : CollatzResearch.WordTrace tailWord_5072580 prefixEnd_5072580 2604671698383868741121635 := by
  unfold tailWord_5072580
  simp only [CollatzResearch.WordTrace]
  refine ⟨92506095981458231268619597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123341461308610975024826129 92506095981458231268619597)
  ·
    refine ⟨34689785993046836725732349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92506095981458231268619597 34689785993046836725732349)
    ·
      refine ⟨13008669747392563772149631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34689785993046836725732349 13008669747392563772149631)
      ·
        refine ⟨19513004621088845658224447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13008669747392563772149631 19513004621088845658224447)
        ·
          refine ⟨29269506931633268487336671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19513004621088845658224447 29269506931633268487336671)
          ·
            refine ⟨43904260397449902731005007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29269506931633268487336671 43904260397449902731005007)
            ·
              refine ⟨65856390596174854096507511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43904260397449902731005007 65856390596174854096507511)
              ·
                refine ⟨98784585894262281144761267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65856390596174854096507511 98784585894262281144761267)
                ·
                  refine ⟨148176878841393421717141901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98784585894262281144761267 148176878841393421717141901)
                  ·
                    refine ⟨55566329565522533143928213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148176878841393421717141901 55566329565522533143928213)
                    ·
                      refine ⟨2604671698383868741121635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55566329565522533143928213 2604671698383868741121635)
                      ·
                        rfl

theorem cell23_5072580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5072580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072580 prefixEnd_5072580 := by exact prefixLift 5072580
  have htrace : WordTrace (prefixWord ++ tailWord_5072580) baseStart_5072580 baseEnd_5072580 := by
    simpa [prefixWord, tailWord_5072580, baseEnd_5072580] using wordTrace_append hprefix tailTrace_5072580
  have hstable : (prefixWord ++ tailWord_5072580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072580).length < 2 ^ (prefixWord ++ tailWord_5072580).sum := by decide
  have hdescent : baseEnd_5072580 < baseStart_5072580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072590 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_5072590 : Nat := 118140960795 + 5072590 * 2 ^ 59
def prefixEnd_5072590 : Nat := 4983230072969 + 3 ^ 40 * 5072590 * 2
def baseEnd_5072590 : Nat := 289408537021157077999621

theorem tailTrace_5072590 : CollatzResearch.WordTrace tailWord_5072590 prefixEnd_5072590 289408537021157077999621 := by
  unfold tailWord_5072590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23126569586610029280637903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123341704461920156163402149 23126569586610029280637903)
  ·
    refine ⟨34689854379915043920956855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23126569586610029280637903 34689854379915043920956855)
    ·
      refine ⟨52034781569872565881435283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34689854379915043920956855 52034781569872565881435283)
      ·
        refine ⟨78052172354808848822152925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52034781569872565881435283 78052172354808848822152925)
        ·
          refine ⟨29269564633053318308307347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78052172354808848822152925 29269564633053318308307347)
          ·
            refine ⟨43904346949579977462461021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29269564633053318308307347 43904346949579977462461021)
            ·
              refine ⟨16464130106092491548422883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43904346949579977462461021 16464130106092491548422883)
              ·
                refine ⟨24696195159138737322634325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16464130106092491548422883 24696195159138737322634325)
                ·
                  refine ⟨289408537021157077999621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24696195159138737322634325 289408537021157077999621)
                  ·
                    rfl

theorem cell23_5072590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_5072590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072590 prefixEnd_5072590 := by exact prefixLift 5072590
  have htrace : WordTrace (prefixWord ++ tailWord_5072590) baseStart_5072590 baseEnd_5072590 := by
    simpa [prefixWord, tailWord_5072590, baseEnd_5072590] using wordTrace_append hprefix tailTrace_5072590
  have hstable : (prefixWord ++ tailWord_5072590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072590).length < 2 ^ (prefixWord ++ tailWord_5072590).sum := by decide
  have hdescent : baseEnd_5072590 < baseStart_5072590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072594 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_5072594 : Nat := 118140960795 + 5072594 * 2 ^ 59
def prefixEnd_5072594 : Nat := 4983230072969 + 3 ^ 40 * 5072594 * 2
def baseEnd_5072594 : Nat := 868226295704343895448857

theorem tailTrace_5072594 : CollatzResearch.WordTrace tailWord_5072594 prefixEnd_5072594 868226295704343895448857 := by
  unfold tailWord_5072594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46253175646216435732062209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123341801723243828618832557 46253175646216435732062209)
  ·
    refine ⟨34689881734662326799046657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46253175646216435732062209 34689881734662326799046657)
    ·
      refine ⟨26017411300996745099284993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34689881734662326799046657 26017411300996745099284993)
      ·
        refine ⟨19513058475747558824463745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26017411300996745099284993 19513058475747558824463745)
        ·
          refine ⟨14634793856810669118347809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19513058475747558824463745 14634793856810669118347809)
          ·
            refine ⟨10976095392608001838760857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14634793856810669118347809 10976095392608001838760857)
            ·
              refine ⟨8232071544456001379070643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10976095392608001838760857 8232071544456001379070643)
              ·
                refine ⟨12348107316684002068605965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8232071544456001379070643 12348107316684002068605965)
                ·
                  refine ⟨4630540243756500775727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12348107316684002068605965 4630540243756500775727237)
                  ·
                    refine ⟨868226295704343895448857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630540243756500775727237 868226295704343895448857)
                    ·
                      rfl

theorem cell23_5072594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_5072594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072594 prefixEnd_5072594 := by exact prefixLift 5072594
  have htrace : WordTrace (prefixWord ++ tailWord_5072594) baseStart_5072594 baseEnd_5072594 := by
    simpa [prefixWord, tailWord_5072594, baseEnd_5072594] using wordTrace_append hprefix tailTrace_5072594
  have hstable : (prefixWord ++ tailWord_5072594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072594).length < 2 ^ (prefixWord ++ tailWord_5072594).sum := by decide
  have hdescent : baseEnd_5072594 < baseStart_5072594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072607 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 6]
def baseStart_5072607 : Nat := 118140960795 + 5072607 * 2 ^ 59
def prefixEnd_5072607 : Nat := 4983230072969 + 3 ^ 40 * 5072607 * 2
def baseEnd_5072607 : Nat := 289409506929060015053779

theorem tailTrace_5072607 : CollatzResearch.WordTrace tailWord_5072607 prefixEnd_5072607 289409506929060015053779 := by
  unfold tailWord_5072607
  simp only [CollatzResearch.WordTrace]
  refine ⟨185013176733818646148472075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123342117822545764098981383 185013176733818646148472075)
  ·
    refine ⟨277519765100727969222708113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185013176733818646148472075 277519765100727969222708113)
    ·
      refine ⟨208139823825545976917031085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277519765100727969222708113 208139823825545976917031085)
      ·
        refine ⟨78052433934579741343886657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208139823825545976917031085 78052433934579741343886657)
        ·
          refine ⟨58539325450934806007914993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78052433934579741343886657 58539325450934806007914993)
          ·
            refine ⟨43904494088201104505936245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58539325450934806007914993 43904494088201104505936245)
            ·
              refine ⟨4116046320768853547431523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43904494088201104505936245 4116046320768853547431523)
              ·
                refine ⟨6174069481153280321147285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116046320768853547431523 6174069481153280321147285)
                ·
                  refine ⟨289409506929060015053779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6174069481153280321147285 289409506929060015053779)
                  ·
                    rfl

theorem cell23_5072607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 6].length) (baseStart_5072607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072607 prefixEnd_5072607 := by exact prefixLift 5072607
  have htrace : WordTrace (prefixWord ++ tailWord_5072607) baseStart_5072607 baseEnd_5072607 := by
    simpa [prefixWord, tailWord_5072607, baseEnd_5072607] using wordTrace_append hprefix tailTrace_5072607
  have hstable : (prefixWord ++ tailWord_5072607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072607).length < 2 ^ (prefixWord ++ tailWord_5072607).sum := by decide
  have hdescent : baseEnd_5072607 < baseStart_5072607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072620 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_5072620 : Nat := 118140960795 + 5072620 * 2 ^ 59
def prefixEnd_5072620 : Nat := 4983230072969 + 3 ^ 40 * 5072620 * 2
def baseEnd_5072620 : Nat := 868230745870016194873817

theorem tailTrace_5072620 : CollatzResearch.WordTrace tailWord_5072620 prefixEnd_5072620 868230745870016194873817 := by
  unfold tailWord_5072620
  simp only [CollatzResearch.WordTrace]
  refine ⟨92506825441385774684347657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123342433921847699579130209 92506825441385774684347657)
  ·
    refine ⟨69380119081039331013260743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92506825441385774684347657 69380119081039331013260743)
    ·
      refine ⟨104070178621558996519891115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69380119081039331013260743 104070178621558996519891115)
      ·
        refine ⟨156105267932338494779836673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104070178621558996519891115 156105267932338494779836673)
        ·
          refine ⟨117078950949253871084877505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156105267932338494779836673 117078950949253871084877505)
          ·
            refine ⟨87809213211940403313658129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117078950949253871084877505 87809213211940403313658129)
            ·
              refine ⟨65856909908955302485243597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87809213211940403313658129 65856909908955302485243597)
              ·
                refine ⟨24696341215858238431966349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65856909908955302485243597 24696341215858238431966349)
                ·
                  refine ⟨9261127955946839411987381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24696341215858238431966349 9261127955946839411987381)
                  ·
                    refine ⟨868230745870016194873817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9261127955946839411987381 868230745870016194873817)
                    ·
                      rfl

theorem cell23_5072620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_5072620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072620 prefixEnd_5072620 := by exact prefixLift 5072620
  have htrace : WordTrace (prefixWord ++ tailWord_5072620) baseStart_5072620 baseEnd_5072620 := by
    simpa [prefixWord, tailWord_5072620, baseEnd_5072620] using wordTrace_append hprefix tailTrace_5072620
  have hstable : (prefixWord ++ tailWord_5072620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072620).length < 2 ^ (prefixWord ++ tailWord_5072620).sum := by decide
  have hdescent : baseEnd_5072620 < baseStart_5072620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072627 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 1, 5, 2]
def baseStart_5072627 : Nat := 118140960795 + 5072627 * 2 ^ 59
def prefixEnd_5072627 : Nat := 4983230072969 + 3 ^ 40 * 5072627 * 2
def baseEnd_5072627 : Nat := 2604695831974630057233919

theorem tailTrace_5072627 : CollatzResearch.WordTrace tailWord_5072627 prefixEnd_5072627 2604695831974630057233919 := by
  unfold tailWord_5072627
  simp only [CollatzResearch.WordTrace]
  refine ⟨185013906193746189564200135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123342604129164126376133423 185013906193746189564200135)
  ·
    refine ⟨277520859290619284346300203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185013906193746189564200135 277520859290619284346300203)
    ·
      refine ⟨416281288935928926519450305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277520859290619284346300203 416281288935928926519450305)
      ·
        refine ⟨312210966701946694889587729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416281288935928926519450305 312210966701946694889587729)
        ·
          refine ⟨234158225026460021167190797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312210966701946694889587729 234158225026460021167190797)
          ·
            refine ⟨87809334384922507937696549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234158225026460021167190797 87809334384922507937696549)
            ·
              refine ⟨16464250197172970238318103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87809334384922507937696549 16464250197172970238318103)
              ·
                refine ⟨24696375295759455357477155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16464250197172970238318103 24696375295759455357477155)
                ·
                  refine ⟨37044562943639183036215733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24696375295759455357477155 37044562943639183036215733)
                  ·
                    refine ⟨3472927775966173409645225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37044562943639183036215733 3472927775966173409645225)
                    ·
                      refine ⟨2604695831974630057233919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472927775966173409645225 2604695831974630057233919)
                      ·
                        rfl

theorem cell23_5072627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5, 2].length) (baseStart_5072627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072627 prefixEnd_5072627 := by exact prefixLift 5072627
  have htrace : WordTrace (prefixWord ++ tailWord_5072627) baseStart_5072627 baseEnd_5072627 := by
    simpa [prefixWord, tailWord_5072627, baseEnd_5072627] using wordTrace_append hprefix tailTrace_5072627
  have hstable : (prefixWord ++ tailWord_5072627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072627).length < 2 ^ (prefixWord ++ tailWord_5072627).sum := by decide
  have hdescent : baseEnd_5072627 < baseStart_5072627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072644 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_5072644 : Nat := 118140960795 + 5072644 * 2 ^ 59
def prefixEnd_5072644 : Nat := 4983230072969 + 3 ^ 40 * 5072644 * 2
def baseEnd_5072644 : Nat := 2604704561145756490721341

theorem tailTrace_5072644 : CollatzResearch.WordTrace tailWord_5072644 prefixEnd_5072644 2604704561145756490721341 := by
  unfold tailWord_5072644
  simp only [CollatzResearch.WordTrace]
  refine ⟨92507263117342300733784493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123343017489789734311712657 92507263117342300733784493)
  ·
    refine ⟨34690223669003362775169185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92507263117342300733784493 34690223669003362775169185)
    ·
      refine ⟨26017667751752522081376889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34690223669003362775169185 26017667751752522081376889)
      ·
        refine ⟨19513250813814391561032667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26017667751752522081376889 19513250813814391561032667)
        ·
          refine ⟨29269876220721587341549001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19513250813814391561032667 29269876220721587341549001)
          ·
            refine ⟨21952407165541190506161751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29269876220721587341549001 21952407165541190506161751)
            ·
              refine ⟨32928610748311785759242627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21952407165541190506161751 32928610748311785759242627)
              ·
                refine ⟨49392916122467678638863941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32928610748311785759242627 49392916122467678638863941)
                ·
                  refine ⟨9261171772962689744786989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49392916122467678638863941 9261171772962689744786989)
                  ·
                    refine ⟨3472939414861008654295121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9261171772962689744786989 3472939414861008654295121)
                    ·
                      refine ⟨2604704561145756490721341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472939414861008654295121 2604704561145756490721341)
                      ·
                        rfl

theorem cell23_5072644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_5072644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072644 prefixEnd_5072644 := by exact prefixLift 5072644
  have htrace : WordTrace (prefixWord ++ tailWord_5072644) baseStart_5072644 baseEnd_5072644 := by
    simpa [prefixWord, tailWord_5072644, baseEnd_5072644] using wordTrace_append hprefix tailTrace_5072644
  have hstable : (prefixWord ++ tailWord_5072644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072644).length < 2 ^ (prefixWord ++ tailWord_5072644).sum := by decide
  have hdescent : baseEnd_5072644 < baseStart_5072644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072667 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 2, 4]
def baseStart_5072667 : Nat := 118140960795 + 5072667 * 2 ^ 59
def prefixEnd_5072667 : Nat := 4983230072969 + 3 ^ 40 * 5072667 * 2
def baseEnd_5072667 : Nat := 868238790400269966911245

theorem tailTrace_5072667 : CollatzResearch.WordTrace tailWord_5072667 prefixEnd_5072667 868238790400269966911245 := by
  unfold tailWord_5072667
  simp only [CollatzResearch.WordTrace]
  refine ⟨185015365113601276395656255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123343576742400850930437503 185015365113601276395656255)
  ·
    refine ⟨277523047670401914593484383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185015365113601276395656255 277523047670401914593484383)
    ·
      refine ⟨416284571505602871890226575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277523047670401914593484383 416284571505602871890226575)
      ·
        refine ⟨624426857258404307835339863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416284571505602871890226575 624426857258404307835339863)
        ·
          refine ⟨936640285887606461753009795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624426857258404307835339863 936640285887606461753009795)
          ·
            refine ⟨1404960428831409692629514693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936640285887606461753009795 1404960428831409692629514693)
            ·
              refine ⟨263430080405889317368034005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1404960428831409692629514693 263430080405889317368034005)
              ·
                refine ⟨6174142509513030875813297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 263430080405889317368034005 6174142509513030875813297)
                ·
                  refine ⟨4630606882134773156859973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6174142509513030875813297 4630606882134773156859973)
                  ·
                    refine ⟨868238790400269966911245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630606882134773156859973 868238790400269966911245)
                    ·
                      rfl

theorem cell23_5072667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 4].length) (baseStart_5072667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072667 prefixEnd_5072667 := by exact prefixLift 5072667
  have htrace : WordTrace (prefixWord ++ tailWord_5072667) baseStart_5072667 baseEnd_5072667 := by
    simpa [prefixWord, tailWord_5072667, baseEnd_5072667] using wordTrace_append hprefix tailTrace_5072667
  have hstable : (prefixWord ++ tailWord_5072667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072667).length < 2 ^ (prefixWord ++ tailWord_5072667).sum := by decide
  have hdescent : baseEnd_5072667 < baseStart_5072667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072691 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 1, 1, 4]
def baseStart_5072691 : Nat := 118140960795 + 5072691 * 2 ^ 59
def prefixEnd_5072691 : Nat := 4983230072969 + 3 ^ 40 * 5072691 * 2
def baseEnd_5072691 : Nat := 2604728694736517806833625

theorem tailTrace_5072691 : CollatzResearch.WordTrace tailWord_5072691 prefixEnd_5072691 2604728694736517806833625 := by
  unfold tailWord_5072691
  simp only [CollatzResearch.WordTrace]
  refine ⟨185016240465514328494529927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123344160310342885663019951 185016240465514328494529927)
  ·
    refine ⟨277524360698271492741794891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185016240465514328494529927 277524360698271492741794891)
    ·
      refine ⟨416286541047407239112692337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277524360698271492741794891 416286541047407239112692337)
      ·
        refine ⟨312214905785555429334519253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416286541047407239112692337 312214905785555429334519253)
        ·
          refine ⟨7317536854348955375027795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 312214905785555429334519253 7317536854348955375027795)
          ·
            refine ⟨10976305281523433062541693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317536854348955375027795 10976305281523433062541693)
            ·
              refine ⟨4116114480571287398453135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10976305281523433062541693 4116114480571287398453135)
              ·
                refine ⟨6174171720856931097679703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116114480571287398453135 6174171720856931097679703)
                ·
                  refine ⟨9261257581285396646519555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6174171720856931097679703 9261257581285396646519555)
                  ·
                    refine ⟨13891886371928094969779333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9261257581285396646519555 13891886371928094969779333)
                    ·
                      refine ⟨2604728694736517806833625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13891886371928094969779333 2604728694736517806833625)
                      ·
                        rfl

theorem cell23_5072691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 1, 4].length) (baseStart_5072691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072691 prefixEnd_5072691 := by exact prefixLift 5072691
  have htrace : WordTrace (prefixWord ++ tailWord_5072691) baseStart_5072691 baseEnd_5072691 := by
    simpa [prefixWord, tailWord_5072691, baseEnd_5072691] using wordTrace_append hprefix tailTrace_5072691
  have hstable : (prefixWord ++ tailWord_5072691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072691).length < 2 ^ (prefixWord ++ tailWord_5072691).sum := by decide
  have hdescent : baseEnd_5072691 < baseStart_5072691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072697 : List Nat := [1, 2, 1, 7, 1, 11]
def baseStart_5072697 : Nat := 118140960795 + 5072697 * 2 ^ 59
def prefixEnd_5072697 : Nat := 4983230072969 + 3 ^ 40 * 5072697 * 2
def baseEnd_5072697 : Nat := 10719060805022406515879

theorem tailTrace_5072697 : CollatzResearch.WordTrace tailWord_5072697 prefixEnd_5072697 10719060805022406515879 := by
  unfold tailWord_5072697
  simp only [CollatzResearch.WordTrace]
  refine ⟨185016459303492591519248345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123344306202328394346165563 185016459303492591519248345)
  ·
    refine ⟨138762344477619443639436259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185016459303492591519248345 138762344477619443639436259)
    ·
      refine ⟨208143516716429165459154389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138762344477619443639436259 208143516716429165459154389)
      ·
        refine ⟨4878363673041308565448931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 208143516716429165459154389 4878363673041308565448931)
        ·
          refine ⟨7317545509561962848173397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878363673041308565448931 7317545509561962848173397)
          ·
            refine ⟨10719060805022406515879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7317545509561962848173397 10719060805022406515879)
            ·
              rfl

theorem cell23_5072697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 11].length) (baseStart_5072697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072697 prefixEnd_5072697 := by exact prefixLift 5072697
  have htrace : WordTrace (prefixWord ++ tailWord_5072697) baseStart_5072697 baseEnd_5072697 := by
    simpa [prefixWord, tailWord_5072697, baseEnd_5072697] using wordTrace_append hprefix tailTrace_5072697
  have hstable : (prefixWord ++ tailWord_5072697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072697).length < 2 ^ (prefixWord ++ tailWord_5072697).sum := by decide
  have hdescent : baseEnd_5072697 < baseStart_5072697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072701 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_5072701 : Nat := 118140960795 + 5072701 * 2 ^ 59
def prefixEnd_5072701 : Nat := 4983230072969 + 3 ^ 40 * 5072701 * 2
def baseEnd_5072701 : Nat := 868244609847687589236193

theorem tailTrace_5072701 : CollatzResearch.WordTrace tailWord_5072701 prefixEnd_5072701 868244609847687589236193 := by
  unfold tailWord_5072701
  simp only [CollatzResearch.WordTrace]
  refine ⟨185016605195478100202393957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123344403463652066801595971 185016605195478100202393957)
  ·
    refine ⟨34690613474152143787948867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185016605195478100202393957 34690613474152143787948867)
    ·
      refine ⟨52035920211228215681923301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34690613474152143787948867 52035920211228215681923301)
      ·
        refine ⟨9756735039605290440360619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52035920211228215681923301 9756735039605290440360619)
        ·
          refine ⟨14635102559407935660540929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9756735039605290440360619 14635102559407935660540929)
          ·
            refine ⟨10976326919555951745405697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14635102559407935660540929 10976326919555951745405697)
            ·
              refine ⟨8232245189666963809054273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10976326919555951745405697 8232245189666963809054273)
              ·
                refine ⟨6174183892250222856790705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8232245189666963809054273 6174183892250222856790705)
                ·
                  refine ⟨4630637919187667142593029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6174183892250222856790705 4630637919187667142593029)
                  ·
                    refine ⟨868244609847687589236193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630637919187667142593029 868244609847687589236193)
                    ·
                      rfl

theorem cell23_5072701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_5072701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072701 prefixEnd_5072701 := by exact prefixLift 5072701
  have htrace : WordTrace (prefixWord ++ tailWord_5072701) baseStart_5072701 baseEnd_5072701 := by
    simpa [prefixWord, tailWord_5072701, baseEnd_5072701] using wordTrace_append hprefix tailTrace_5072701
  have hstable : (prefixWord ++ tailWord_5072701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072701).length < 2 ^ (prefixWord ++ tailWord_5072701).sum := by decide
  have hdescent : baseEnd_5072701 < baseStart_5072701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072720 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_5072720 : Nat := 118140960795 + 5072720 * 2 ^ 59
def prefixEnd_5072720 : Nat := 4983230072969 + 3 ^ 40 * 5072720 * 2
def baseEnd_5072720 : Nat := 2604743585675498193370991

theorem tailTrace_5072720 : CollatzResearch.WordTrace tailWord_5072720 prefixEnd_5072720 2604743585675498193370991 := by
  unfold tailWord_5072720
  simp only [CollatzResearch.WordTrace]
  refine ⟨92508649091204633223667807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123344865454939510964890409 92508649091204633223667807)
  ·
    refine ⟨138762973636806949835501711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92508649091204633223667807 138762973636806949835501711)
    ·
      refine ⟨208144460455210424753252567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138762973636806949835501711 208144460455210424753252567)
      ·
        refine ⟨312216690682815637129878851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208144460455210424753252567 312216690682815637129878851)
        ·
          refine ⟨468325036024223455694818277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312216690682815637129878851 468325036024223455694818277)
          ·
            refine ⟨87810944254541897942778427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 468325036024223455694818277 87810944254541897942778427)
            ·
              refine ⟨131716416381812846914167641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87810944254541897942778427 131716416381812846914167641)
              ·
                refine ⟨98787312286359635185625731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131716416381812846914167641 98787312286359635185625731)
                ·
                  refine ⟨148180968429539452778438597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98787312286359635185625731 148180968429539452778438597)
                  ·
                    refine ⟨27783931580538647395957237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148180968429539452778438597 27783931580538647395957237)
                    ·
                      refine ⟨2604743585675498193370991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27783931580538647395957237 2604743585675498193370991)
                      ·
                        rfl

theorem cell23_5072720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_5072720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072720 prefixEnd_5072720 := by exact prefixLift 5072720
  have htrace : WordTrace (prefixWord ++ tailWord_5072720) baseStart_5072720 baseEnd_5072720 := by
    simpa [prefixWord, tailWord_5072720, baseEnd_5072720] using wordTrace_append hprefix tailTrace_5072720
  have hstable : (prefixWord ++ tailWord_5072720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072720).length < 2 ^ (prefixWord ++ tailWord_5072720).sum := by decide
  have hdescent : baseEnd_5072720 < baseStart_5072720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072724 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_5072724 : Nat := 118140960795 + 5072724 * 2 ^ 59
def prefixEnd_5072724 : Nat := 4983230072969 + 3 ^ 40 * 5072724 * 2
def baseEnd_5072724 : Nat := 2604745639598116177720973

theorem tailTrace_5072724 : CollatzResearch.WordTrace tailWord_5072724 prefixEnd_5072724 2604745639598116177720973 := by
  unfold tailWord_5072724
  simp only [CollatzResearch.WordTrace]
  refine ⟨92508722037197387565240613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123344962716263183420320817 92508722037197387565240613)
  ·
    refine ⟨17345385381974510168482615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92508722037197387565240613 17345385381974510168482615)
    ·
      refine ⟨26018078072961765252723923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17345385381974510168482615 26018078072961765252723923)
      ·
        refine ⟨39027117109442647879085885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26018078072961765252723923 39027117109442647879085885)
        ·
          refine ⟨14635168916040992954657207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39027117109442647879085885 14635168916040992954657207)
          ·
            refine ⟨21952753374061489431985811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14635168916040992954657207 21952753374061489431985811)
            ·
              refine ⟨32929130061092234147978717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21952753374061489431985811 32929130061092234147978717)
              ·
                refine ⟨12348423772909587805492019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32929130061092234147978717 12348423772909587805492019)
                ·
                  refine ⟨18522635659364381708238029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12348423772909587805492019 18522635659364381708238029)
                  ·
                    refine ⟨6945988372261643140589261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18522635659364381708238029 6945988372261643140589261)
                    ·
                      refine ⟨2604745639598116177720973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6945988372261643140589261 2604745639598116177720973)
                      ·
                        rfl

theorem cell23_5072724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_5072724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072724 prefixEnd_5072724 := by exact prefixLift 5072724
  have htrace : WordTrace (prefixWord ++ tailWord_5072724) baseStart_5072724 baseEnd_5072724 := by
    simpa [prefixWord, tailWord_5072724, baseEnd_5072724] using wordTrace_append hprefix tailTrace_5072724
  have hstable : (prefixWord ++ tailWord_5072724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072724).length < 2 ^ (prefixWord ++ tailWord_5072724).sum := by decide
  have hdescent : baseEnd_5072724 < baseStart_5072724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072757 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_5072757 : Nat := 118140960795 + 5072757 * 2 ^ 59
def prefixEnd_5072757 : Nat := 4983230072969 + 3 ^ 40 * 5072757 * 2
def baseEnd_5072757 : Nat := 868254194819904849536107

theorem tailTrace_5072757 : CollatzResearch.WordTrace tailWord_5072757 prefixEnd_5072757 868254194819904849536107 := by
  unfold tailWord_5072757
  simp only [CollatzResearch.WordTrace]
  refine ⟨185018647683275221766432525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123345765122183481177621683 185018647683275221766432525)
  ·
    refine ⟨69381992881228208162412197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185018647683275221766432525 69381992881228208162412197)
    ·
      refine ⟨13009123665230289030452287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69381992881228208162412197 13009123665230289030452287)
      ·
        refine ⟨19513685497845433545678431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13009123665230289030452287 19513685497845433545678431)
        ·
          refine ⟨29270528246768150318517647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19513685497845433545678431 29270528246768150318517647)
          ·
            refine ⟨43905792370152225477776471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29270528246768150318517647 43905792370152225477776471)
            ·
              refine ⟨65858688555228338216664707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43905792370152225477776471 65858688555228338216664707)
              ·
                refine ⟨98788032832842507324997061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65858688555228338216664707 98788032832842507324997061)
                ·
                  refine ⟨18522756156157970123436949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98788032832842507324997061 18522756156157970123436949)
                  ·
                    refine ⟨868254194819904849536107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18522756156157970123436949 868254194819904849536107)
                    ·
                      rfl

theorem cell23_5072757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_5072757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072757 prefixEnd_5072757 := by exact prefixLift 5072757
  have htrace : WordTrace (prefixWord ++ tailWord_5072757) baseStart_5072757 baseEnd_5072757 := by
    simpa [prefixWord, tailWord_5072757, baseEnd_5072757] using wordTrace_append hprefix tailTrace_5072757
  have hstable : (prefixWord ++ tailWord_5072757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072757).length < 2 ^ (prefixWord ++ tailWord_5072757).sum := by decide
  have hdescent : baseEnd_5072757 < baseStart_5072757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072758 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5072758 : Nat := 118140960795 + 5072758 * 2 ^ 59
def prefixEnd_5072758 : Nat := 4983230072969 + 3 ^ 40 * 5072758 * 2
def baseEnd_5072758 : Nat := 2604763097940369044695817

theorem tailTrace_5072758 : CollatzResearch.WordTrace tailWord_5072758 prefixEnd_5072758 2604763097940369044695817 := by
  unfold tailWord_5072758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11563667759766974933576183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123345789437514399291479285 11563667759766974933576183)
  ·
    refine ⟨17345501639650462400364275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11563667759766974933576183 17345501639650462400364275)
    ·
      refine ⟨26018252459475693600546413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17345501639650462400364275 26018252459475693600546413)
      ·
        refine ⟨9756844672303385100204905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26018252459475693600546413 9756844672303385100204905)
        ·
          refine ⟨7317633504227538825153679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9756844672303385100204905 7317633504227538825153679)
          ·
            refine ⟨10976450256341308237730519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317633504227538825153679 10976450256341308237730519)
            ·
              refine ⟨16464675384511962356595779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10976450256341308237730519 16464675384511962356595779)
              ·
                refine ⟨24697013076767943534893669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16464675384511962356595779 24697013076767943534893669)
                ·
                  refine ⟨4630689951893989412792563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24697013076767943534893669 4630689951893989412792563)
                  ·
                    refine ⟨6946034927840984119188845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4630689951893989412792563 6946034927840984119188845)
                    ·
                      refine ⟨2604763097940369044695817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6946034927840984119188845 2604763097940369044695817)
                      ·
                        rfl

theorem cell23_5072758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5072758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072758 prefixEnd_5072758 := by exact prefixLift 5072758
  have htrace : WordTrace (prefixWord ++ tailWord_5072758) baseStart_5072758 baseEnd_5072758 := by
    simpa [prefixWord, tailWord_5072758, baseEnd_5072758] using wordTrace_append hprefix tailTrace_5072758
  have hstable : (prefixWord ++ tailWord_5072758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072758).length < 2 ^ (prefixWord ++ tailWord_5072758).sum := by decide
  have hdescent : baseEnd_5072758 < baseStart_5072758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072777 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_5072777 : Nat := 118140960795 + 5072777 * 2 ^ 59
def prefixEnd_5072777 : Nat := 4983230072969 + 3 ^ 40 * 5072777 * 2
def baseEnd_5072777 : Nat := 2604772854072804470358229

theorem tailTrace_5072777 : CollatzResearch.WordTrace tailWord_5072777 prefixEnd_5072777 2604772854072804470358229 := by
  unfold tailWord_5072777
  simp only [CollatzResearch.WordTrace]
  refine ⟨185019377143202765182160585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123346251428801843454773723 185019377143202765182160585)
  ·
    refine ⟨138764532857402073886620439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185019377143202765182160585 138764532857402073886620439)
    ·
      refine ⟨208146799286103110829930659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138764532857402073886620439 208146799286103110829930659)
      ·
        refine ⟨312220198929154666244895989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208146799286103110829930659 312220198929154666244895989)
        ·
          refine ⟨29270643649608249960458999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 312220198929154666244895989 29270643649608249960458999)
          ·
            refine ⟨43905965474412374940688499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29270643649608249960458999 43905965474412374940688499)
            ·
              refine ⟨65858948211618562411032749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43905965474412374940688499 65858948211618562411032749)
              ·
                refine ⟨24697105579356960904137281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65858948211618562411032749 24697105579356960904137281)
                ·
                  refine ⟨18522829184517720678102961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24697105579356960904137281 18522829184517720678102961)
                  ·
                    refine ⟨13892121888388290508577221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18522829184517720678102961 13892121888388290508577221)
                    ·
                      refine ⟨2604772854072804470358229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13892121888388290508577221 2604772854072804470358229)
                      ·
                        rfl

theorem cell23_5072777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_5072777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072777 prefixEnd_5072777 := by exact prefixLift 5072777
  have htrace : WordTrace (prefixWord ++ tailWord_5072777) baseStart_5072777 baseEnd_5072777 := by
    simpa [prefixWord, tailWord_5072777, baseEnd_5072777] using wordTrace_append hprefix tailTrace_5072777
  have hstable : (prefixWord ++ tailWord_5072777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072777).length < 2 ^ (prefixWord ++ tailWord_5072777).sum := by decide
  have hdescent : baseEnd_5072777 < baseStart_5072777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072824 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 2, 5, 2]
def baseStart_5072824 : Nat := 118140960795 + 5072824 * 2 ^ 59
def prefixEnd_5072824 : Nat := 4983230072969 + 3 ^ 40 * 5072824 * 2
def baseEnd_5072824 : Nat := 2604796987663565786470513

theorem tailTrace_5072824 : CollatzResearch.WordTrace tailWord_5072824 prefixEnd_5072824 2604796987663565786470513 := by
  unfold tailWord_5072824
  simp only [CollatzResearch.WordTrace]
  refine ⟨92510545687016246104560763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123347394249354994806081017 92510545687016246104560763)
  ·
    refine ⟨138765818530524369156841145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92510545687016246104560763 138765818530524369156841145)
    ·
      refine ⟨104074363897893276867630859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138765818530524369156841145 104074363897893276867630859)
      ·
        refine ⟨156111545846839915301446289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104074363897893276867630859 156111545846839915301446289)
        ·
          refine ⟨117083659385129936476084717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156111545846839915301446289 117083659385129936476084717)
          ·
            refine ⟨43906372269423726178531769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117083659385129936476084717 43906372269423726178531769)
            ·
              refine ⟨32929779202067794633898827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43906372269423726178531769 32929779202067794633898827)
              ·
                refine ⟨49394668803101691950848241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32929779202067794633898827 49394668803101691950848241)
                ·
                  refine ⟨37046001602326268963136181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49394668803101691950848241 37046001602326268963136181)
                  ·
                    refine ⟨3473062650218087715294017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37046001602326268963136181 3473062650218087715294017)
                    ·
                      refine ⟨2604796987663565786470513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473062650218087715294017 2604796987663565786470513)
                      ·
                        rfl

theorem cell23_5072824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_5072824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072824 prefixEnd_5072824 := by exact prefixLift 5072824
  have htrace : WordTrace (prefixWord ++ tailWord_5072824) baseStart_5072824 baseEnd_5072824 := by
    simpa [prefixWord, tailWord_5072824, baseEnd_5072824] using wordTrace_append hprefix tailTrace_5072824
  have hstable : (prefixWord ++ tailWord_5072824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072824).length < 2 ^ (prefixWord ++ tailWord_5072824).sum := by decide
  have hdescent : baseEnd_5072824 < baseStart_5072824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072837 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_5072837 : Nat := 118140960795 + 5072837 * 2 ^ 59
def prefixEnd_5072837 : Nat := 4983230072969 + 3 ^ 40 * 5072837 * 2
def baseEnd_5072837 : Nat := 2604803662912074235607953

theorem tailTrace_5072837 : CollatzResearch.WordTrace tailWord_5072837 prefixEnd_5072837 2604803662912074235607953 := by
  unfold tailWord_5072837
  simp only [CollatzResearch.WordTrace]
  refine ⟨185021565522985395429344765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123347710348656930286229843 185021565522985395429344765)
  ·
    refine ⟨69383087071119523286004287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185021565522985395429344765 69383087071119523286004287)
    ·
      refine ⟨104074630606679284929006431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69383087071119523286004287 104074630606679284929006431)
      ·
        refine ⟨156111945910018927393509647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104074630606679284929006431 156111945910018927393509647)
        ·
          refine ⟨234167918865028391090264471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156111945910018927393509647 234167918865028391090264471)
          ·
            refine ⟨351251878297542586635396707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234167918865028391090264471 351251878297542586635396707)
            ·
              refine ⟨526877817446313879953095061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351251878297542586635396707 526877817446313879953095061)
              ·
                refine ⟨24697397692795963122801331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 526877817446313879953095061 24697397692795963122801331)
                ·
                  refine ⟨37046096539193944684201997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24697397692795963122801331 37046096539193944684201997)
                  ·
                    refine ⟨13892286202197729256575749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37046096539193944684201997 13892286202197729256575749)
                    ·
                      refine ⟨2604803662912074235607953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13892286202197729256575749 2604803662912074235607953)
                      ·
                        rfl

theorem cell23_5072837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_5072837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072837 prefixEnd_5072837 := by exact prefixLift 5072837
  have htrace : WordTrace (prefixWord ++ tailWord_5072837) baseStart_5072837 baseEnd_5072837 := by
    simpa [prefixWord, tailWord_5072837, baseEnd_5072837] using wordTrace_append hprefix tailTrace_5072837
  have hstable : (prefixWord ++ tailWord_5072837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072837).length < 2 ^ (prefixWord ++ tailWord_5072837).sum := by decide
  have hdescent : baseEnd_5072837 < baseStart_5072837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072931 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 4, 3, 2]
def baseStart_5072931 : Nat := 118140960795 + 5072931 * 2 ^ 59
def prefixEnd_5072931 : Nat := 4983230072969 + 3 ^ 40 * 5072931 * 2
def baseEnd_5072931 : Nat := 2604851930093596867832521

theorem tailTrace_5072931 : CollatzResearch.WordTrace tailWord_5072931 prefixEnd_5072931 2604851930093596867832521 := by
  unfold tailWord_5072931
  simp only [CollatzResearch.WordTrace]
  refine ⟨185024993984644849483266647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123349995989763232988844431 185024993984644849483266647)
  ·
    refine ⟨277537490976967274224899971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185024993984644849483266647 277537490976967274224899971)
    ·
      refine ⟨416306236465450911337349957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277537490976967274224899971 416306236465450911337349957)
      ·
        refine ⟨78057419337272045875753117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 416306236465450911337349957 78057419337272045875753117)
        ·
          refine ⟨29271532251477017203407419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78057419337272045875753117 29271532251477017203407419)
          ·
            refine ⟨43907298377215525805111129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29271532251477017203407419 43907298377215525805111129)
            ·
              refine ⟨32930473782911644353833347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43907298377215525805111129 32930473782911644353833347)
              ·
                refine ⟨49395710674367466530750021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32930473782911644353833347 49395710674367466530750021)
                ·
                  refine ⟨9261695751443899974515629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49395710674367466530750021 9261695751443899974515629)
                  ·
                    refine ⟨3473135906791462490443361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9261695751443899974515629 3473135906791462490443361)
                    ·
                      refine ⟨2604851930093596867832521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473135906791462490443361 2604851930093596867832521)
                      ·
                        rfl

theorem cell23_5072931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_5072931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072931 prefixEnd_5072931 := by exact prefixLift 5072931
  have htrace : WordTrace (prefixWord ++ tailWord_5072931) baseStart_5072931 baseEnd_5072931 := by
    simpa [prefixWord, tailWord_5072931, baseEnd_5072931] using wordTrace_append hprefix tailTrace_5072931
  have hstable : (prefixWord ++ tailWord_5072931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072931).length < 2 ^ (prefixWord ++ tailWord_5072931).sum := by decide
  have hdescent : baseEnd_5072931 < baseStart_5072931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072938 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_5072938 : Nat := 118140960795 + 5072938 * 2 ^ 59
def prefixEnd_5072938 : Nat := 4983230072969 + 3 ^ 40 * 5072938 * 2
def baseEnd_5072938 : Nat := 2604855524458178340444989

theorem tailTrace_5072938 : CollatzResearch.WordTrace tailWord_5072938 prefixEnd_5072938 2604855524458178340444989 := by
  unfold tailWord_5072938
  simp only [CollatzResearch.WordTrace]
  refine ⟨46256312323904872419692867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123350166197079659785847645 46256312323904872419692867)
  ·
    refine ⟨69384468485857308629539301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46256312323904872419692867 69384468485857308629539301)
    ·
      refine ⟨13009587841098245368038619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69384468485857308629539301 13009587841098245368038619)
      ·
        refine ⟨19514381761647368052057929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13009587841098245368038619 19514381761647368052057929)
        ·
          refine ⟨14635786321235526039043447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19514381761647368052057929 14635786321235526039043447)
          ·
            refine ⟨21953679481853289058565171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14635786321235526039043447 21953679481853289058565171)
            ·
              refine ⟨32930519222779933587847757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21953679481853289058565171 32930519222779933587847757)
              ·
                refine ⟨12348944708542475095442909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32930519222779933587847757 12348944708542475095442909)
                ·
                  refine ⟨4630854265703428160791091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12348944708542475095442909 4630854265703428160791091)
                  ·
                    refine ⟨6946281398555142241186637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4630854265703428160791091 6946281398555142241186637)
                    ·
                      refine ⟨2604855524458178340444989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6946281398555142241186637 2604855524458178340444989)
                      ·
                        rfl

theorem cell23_5072938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_5072938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072938 prefixEnd_5072938 := by exact prefixLift 5072938
  have htrace : WordTrace (prefixWord ++ tailWord_5072938) baseStart_5072938 baseEnd_5072938 := by
    simpa [prefixWord, tailWord_5072938, baseEnd_5072938] using wordTrace_append hprefix tailTrace_5072938
  have hstable : (prefixWord ++ tailWord_5072938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072938).length < 2 ^ (prefixWord ++ tailWord_5072938).sum := by decide
  have hdescent : baseEnd_5072938 < baseStart_5072938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072981 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_5072981 : Nat := 118140960795 + 5072981 * 2 ^ 59
def prefixEnd_5072981 : Nat := 4983230072969 + 3 ^ 40 * 5072981 * 2
def baseEnd_5072981 : Nat := 2604877604126321672207291

theorem tailTrace_5072981 : CollatzResearch.WordTrace tailWord_5072981 prefixEnd_5072981 2604877604126321672207291 := by
  unfold tailWord_5072981
  simp only [CollatzResearch.WordTrace]
  refine ⟨185026817634463708022586797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123351211756309138681724531 185026817634463708022586797)
  ·
    refine ⟨69385056612923890508470049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185026817634463708022586797 69385056612923890508470049)
    ·
      refine ⟨52038792459692917881352537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69385056612923890508470049 52038792459692917881352537)
      ·
        refine ⟨39029094344769688411014403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52038792459692917881352537 39029094344769688411014403)
        ·
          refine ⟨58543641517154532616521605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39029094344769688411014403 58543641517154532616521605)
          ·
            refine ⟨10976932784466474865597801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58543641517154532616521605 10976932784466474865597801)
            ·
              refine ⟨8232699588349856149198351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10976932784466474865597801 8232699588349856149198351)
              ·
                refine ⟨12349049382524784223797527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8232699588349856149198351 12349049382524784223797527)
                ·
                  refine ⟨18523574073787176335696291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12349049382524784223797527 18523574073787176335696291)
                  ·
                    refine ⟨27785361110680764503544437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18523574073787176335696291 27785361110680764503544437)
                    ·
                      refine ⟨2604877604126321672207291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27785361110680764503544437 2604877604126321672207291)
                      ·
                        rfl

theorem cell23_5072981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_5072981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072981 prefixEnd_5072981 := by exact prefixLift 5072981
  have htrace : WordTrace (prefixWord ++ tailWord_5072981) baseStart_5072981 baseEnd_5072981 := by
    simpa [prefixWord, tailWord_5072981, baseEnd_5072981] using wordTrace_append hprefix tailTrace_5072981
  have hstable : (prefixWord ++ tailWord_5072981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072981).length < 2 ^ (prefixWord ++ tailWord_5072981).sum := by decide
  have hdescent : baseEnd_5072981 < baseStart_5072981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072982 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5072982 : Nat := 118140960795 + 5072982 * 2 ^ 59
def prefixEnd_5072982 : Nat := 4983230072969 + 3 ^ 40 * 5072982 * 2
def baseEnd_5072982 : Nat := 2604878117606976168294787

theorem tailTrace_5072982 : CollatzResearch.WordTrace tailWord_5072982 prefixEnd_5072982 2604878117606976168294787 := by
  unfold tailWord_5072982
  simp only [CollatzResearch.WordTrace]
  refine ⟨11564178381716255324585825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123351236071640056795582133 11564178381716255324585825)
  ·
    refine ⟨8673133786287191493439369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11564178381716255324585825 8673133786287191493439369)
    ·
      refine ⟨6504850339715393620079527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8673133786287191493439369 6504850339715393620079527)
      ·
        refine ⟨9757275509573090430119291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504850339715393620079527 9757275509573090430119291)
        ·
          refine ⟨14635913264359635645178937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9757275509573090430119291 14635913264359635645178937)
          ·
            refine ⟨10976934948269726733884203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14635913264359635645178937 10976934948269726733884203)
            ·
              refine ⟨16465402422404590100826305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10976934948269726733884203 16465402422404590100826305)
              ·
                refine ⟨12349051816803442575619729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16465402422404590100826305 12349051816803442575619729)
                ·
                  refine ⟨9261788862602581931714797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12349051816803442575619729 9261788862602581931714797)
                  ·
                    refine ⟨3473170823475968224393049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9261788862602581931714797 3473170823475968224393049)
                    ·
                      refine ⟨2604878117606976168294787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473170823475968224393049 2604878117606976168294787)
                      ·
                        rfl

theorem cell23_5072982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5072982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072982 prefixEnd_5072982 := by exact prefixLift 5072982
  have htrace : WordTrace (prefixWord ++ tailWord_5072982) baseStart_5072982 baseEnd_5072982 := by
    simpa [prefixWord, tailWord_5072982, baseEnd_5072982] using wordTrace_append hprefix tailTrace_5072982
  have hstable : (prefixWord ++ tailWord_5072982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072982).length < 2 ^ (prefixWord ++ tailWord_5072982).sum := by decide
  have hdescent : baseEnd_5072982 < baseStart_5072982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072984 : List Nat := [2, 1, 2, 2, 1, 6, 9]
def baseStart_5072984 : Nat := 118140960795 + 5072984 * 2 ^ 59
def prefixEnd_5072984 : Nat := 4983230072969 + 3 ^ 40 * 5072984 * 2
def baseEnd_5072984 : Nat := 32159001784793643956417

theorem tailTrace_5072984 : CollatzResearch.WordTrace tailWord_5072984 prefixEnd_5072984 32159001784793643956417 := by
  unfold tailWord_5072984
  simp only [CollatzResearch.WordTrace]
  refine ⟨92513463526726419767473003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123351284702301893023297337 92513463526726419767473003)
  ·
    refine ⟨138770195290089629651209505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92513463526726419767473003 138770195290089629651209505)
    ·
      refine ⟨104077646467567222238407129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138770195290089629651209505 104077646467567222238407129)
      ·
        refine ⟨78058234850675416678805347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104077646467567222238407129 78058234850675416678805347)
        ·
          refine ⟨117087352276013125018208021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78058234850675416678805347 117087352276013125018208021)
          ·
            refine ⟨5488469637938115235228501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117087352276013125018208021 5488469637938115235228501)
            ·
              refine ⟨32159001784793643956417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5488469637938115235228501 32159001784793643956417)
              ·
                rfl

theorem cell23_5072984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 9].length) (baseStart_5072984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072984 prefixEnd_5072984 := by exact prefixLift 5072984
  have htrace : WordTrace (prefixWord ++ tailWord_5072984) baseStart_5072984 baseEnd_5072984 := by
    simpa [prefixWord, tailWord_5072984, baseEnd_5072984] using wordTrace_append hprefix tailTrace_5072984
  have hstable : (prefixWord ++ tailWord_5072984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072984).length < 2 ^ (prefixWord ++ tailWord_5072984).sum := by decide
  have hdescent : baseEnd_5072984 < baseStart_5072984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072989 : List Nat := [1, 4, 4, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5072989 : Nat := 118140960795 + 5072989 * 2 ^ 59
def prefixEnd_5072989 : Nat := 4983230072969 + 3 ^ 40 * 5072989 * 2
def baseEnd_5072989 : Nat := 2604881711971557640907255

theorem tailTrace_5072989 : CollatzResearch.WordTrace tailWord_5072989 prefixEnd_5072989 2604881711971557640907255 := by
  unfold tailWord_5072989
  simp only [CollatzResearch.WordTrace]
  refine ⟨185027109418434725388878021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123351406278956483592585347 185027109418434725388878021)
  ·
    refine ⟨34692583015956511010414629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185027109418434725388878021 34692583015956511010414629)
    ·
      refine ⟨6504859315491845814452743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34692583015956511010414629 6504859315491845814452743)
      ·
        refine ⟨9757288973237768721679115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504859315491845814452743 9757288973237768721679115)
        ·
          refine ⟨14635933459856653082518673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9757288973237768721679115 14635933459856653082518673)
          ·
            refine ⟨10976950094892489811889005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14635933459856653082518673 10976950094892489811889005)
            ·
              refine ⟨4116356285584683679458377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10976950094892489811889005 4116356285584683679458377)
              ·
                refine ⟨3087267214188512759593783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116356285584683679458377 3087267214188512759593783)
                ·
                  refine ⟨4630900821282769139390675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087267214188512759593783 4630900821282769139390675)
                  ·
                    refine ⟨6946351231924153709086013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4630900821282769139390675 6946351231924153709086013)
                    ·
                      refine ⟨2604881711971557640907255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6946351231924153709086013 2604881711971557640907255)
                      ·
                        rfl

theorem cell23_5072989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5072989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072989 prefixEnd_5072989 := by exact prefixLift 5072989
  have htrace : WordTrace (prefixWord ++ tailWord_5072989) baseStart_5072989 baseEnd_5072989 := by
    simpa [prefixWord, tailWord_5072989, baseEnd_5072989] using wordTrace_append hprefix tailTrace_5072989
  have hstable : (prefixWord ++ tailWord_5072989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072989).length < 2 ^ (prefixWord ++ tailWord_5072989).sum := by decide
  have hdescent : baseEnd_5072989 < baseStart_5072989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5072995 : List Nat := [1, 1, 1, 5, 1, 1, 2, 6, 1, 2, 2]
def baseStart_5072995 : Nat := 118140960795 + 5072995 * 2 ^ 59
def prefixEnd_5072995 : Nat := 4983230072969 + 3 ^ 40 * 5072995 * 2
def baseEnd_5072995 : Nat := 2604884792855484617432227

theorem tailTrace_5072995 : CollatzResearch.WordTrace tailWord_5072995 prefixEnd_5072995 2604884792855484617432227 := by
  unfold tailWord_5072995
  simp only [CollatzResearch.WordTrace]
  refine ⟨185027328256412988413596439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123351552170941992275730959 185027328256412988413596439)
  ·
    refine ⟨277540992384619482620394659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185027328256412988413596439 277540992384619482620394659)
    ·
      refine ⟨416311488576929223930591989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277540992384619482620394659 416311488576929223930591989)
      ·
        refine ⟨39029202054087114743492999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 416311488576929223930591989 39029202054087114743492999)
        ·
          refine ⟨58543803081130672115239499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39029202054087114743492999 58543803081130672115239499)
          ·
            refine ⟨87815704621696008172859249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58543803081130672115239499 87815704621696008172859249)
            ·
              refine ⟨65861778466272006129644437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87815704621696008172859249 65861778466272006129644437)
              ·
                refine ⟨3087270865606500287327083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65861778466272006129644437 3087270865606500287327083)
                ·
                  refine ⟨4630906298409750430990625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087270865606500287327083 4630906298409750430990625)
                  ·
                    refine ⟨3473179723807312823242969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4630906298409750430990625 3473179723807312823242969)
                    ·
                      refine ⟨2604884792855484617432227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473179723807312823242969 2604884792855484617432227)
                      ·
                        rfl

theorem cell23_5072995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_5072995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5072995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5072995 prefixEnd_5072995 := by exact prefixLift 5072995
  have htrace : WordTrace (prefixWord ++ tailWord_5072995) baseStart_5072995 baseEnd_5072995 := by
    simpa [prefixWord, tailWord_5072995, baseEnd_5072995] using wordTrace_append hprefix tailTrace_5072995
  have hstable : (prefixWord ++ tailWord_5072995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5072995).length < 2 ^ (prefixWord ++ tailWord_5072995).sum := by decide
  have hdescent : baseEnd_5072995 < baseStart_5072995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5072995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073051 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 3, 4, 2]
def baseStart_5073051 : Nat := 118140960795 + 5073051 * 2 ^ 59
def prefixEnd_5073051 : Nat := 4983230072969 + 3 ^ 40 * 5073051 * 2
def baseEnd_5073051 : Nat := 2604913547772136398331969

theorem tailTrace_5073051 : CollatzResearch.WordTrace tailWord_5073051 prefixEnd_5073051 2604913547772136398331969 := by
  unfold tailWord_5073051
  simp only [CollatzResearch.WordTrace]
  refine ⟨185029370744210109977635007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123352913829473406651756671 185029370744210109977635007)
  ·
    refine ⟨277544056116315164966452511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185029370744210109977635007 277544056116315164966452511)
    ·
      refine ⟨416316084174472747449678767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277544056116315164966452511 416316084174472747449678767)
      ·
        refine ⟨624474126261709121174518151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416316084174472747449678767 624474126261709121174518151)
        ·
          refine ⟨936711189392563681761777227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624474126261709121174518151 936711189392563681761777227)
          ·
            refine ⟨1405066784088845522642665841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936711189392563681761777227 1405066784088845522642665841)
            ·
              refine ⟨1053800088066634141981999381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405066784088845522642665841 1053800088066634141981999381)
              ·
                refine ⟨49396879128123475405406221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1053800088066634141981999381 49396879128123475405406221)
                ·
                  refine ⟨18523829673046303277027333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49396879128123475405406221 18523829673046303277027333)
                  ·
                    refine ⟨3473218063696181864442625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18523829673046303277027333 3473218063696181864442625)
                    ·
                      refine ⟨2604913547772136398331969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473218063696181864442625 2604913547772136398331969)
                      ·
                        rfl

theorem cell23_5073051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4, 2].length) (baseStart_5073051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073051 prefixEnd_5073051 := by exact prefixLift 5073051
  have htrace : WordTrace (prefixWord ++ tailWord_5073051) baseStart_5073051 baseEnd_5073051 := by
    simpa [prefixWord, tailWord_5073051, baseEnd_5073051] using wordTrace_append hprefix tailTrace_5073051
  have hstable : (prefixWord ++ tailWord_5073051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073051).length < 2 ^ (prefixWord ++ tailWord_5073051).sum := by decide
  have hdescent : baseEnd_5073051 < baseStart_5073051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073102 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_5073102 : Nat := 118140960795 + 5073102 * 2 ^ 59
def prefixEnd_5073102 : Nat := 4983230072969 + 3 ^ 40 * 5073102 * 2
def baseEnd_5073102 : Nat := 2604939735285515698794235

theorem tailTrace_5073102 : CollatzResearch.WordTrace tailWord_5073102 prefixEnd_5073102 2604939735285515698794235 := by
  unfold tailWord_5073102
  simp only [CollatzResearch.WordTrace]
  refine ⟨23128903858378168210967695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123354153911350230458494373 23128903858378168210967695)
  ·
    refine ⟨34693355787567252316451543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23128903858378168210967695 34693355787567252316451543)
    ·
      refine ⟨52040033681350878474677315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34693355787567252316451543 52040033681350878474677315)
      ·
        refine ⟨78060050522026317712015973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52040033681350878474677315 78060050522026317712015973)
        ·
          refine ⟨14636259472879934571002995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78060050522026317712015973 14636259472879934571002995)
          ·
            refine ⟨21954389209319901856504493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14636259472879934571002995 21954389209319901856504493)
            ·
              refine ⟨8232895953494963196189185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21954389209319901856504493 8232895953494963196189185)
              ·
                refine ⟨6174671965121222397141889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8232895953494963196189185 6174671965121222397141889)
                ·
                  refine ⟨4631003973840916797856417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6174671965121222397141889 4631003973840916797856417)
                  ·
                    refine ⟨3473252980380687598392313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631003973840916797856417 3473252980380687598392313)
                    ·
                      refine ⟨2604939735285515698794235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473252980380687598392313 2604939735285515698794235)
                      ·
                        rfl

theorem cell23_5073102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_5073102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073102 prefixEnd_5073102 := by exact prefixLift 5073102
  have htrace : WordTrace (prefixWord ++ tailWord_5073102) baseStart_5073102 baseEnd_5073102 := by
    simpa [prefixWord, tailWord_5073102, baseEnd_5073102] using wordTrace_append hprefix tailTrace_5073102
  have hstable : (prefixWord ++ tailWord_5073102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073102).length < 2 ^ (prefixWord ++ tailWord_5073102).sum := by decide
  have hdescent : baseEnd_5073102 < baseStart_5073102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073246 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5073246 : Nat := 118140960795 + 5073246 * 2 ^ 59
def prefixEnd_5073246 : Nat := 4983230072969 + 3 ^ 40 * 5073246 * 2
def baseEnd_5073246 : Nat := 2605013676499763135393573

theorem tailTrace_5073246 : CollatzResearch.WordTrace tailWord_5073246 prefixEnd_5073246 2605013676499763135393573 := by
  unfold tailWord_5073246
  simp only [CollatzResearch.WordTrace]
  refine ⟨23129560372312957285122949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123357655319002438853989061 23129560372312957285122949)
  ·
    refine ⟨4336792569808679490960553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23129560372312957285122949 4336792569808679490960553)
    ·
      refine ⟨3252594427356509618220415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4336792569808679490960553 3252594427356509618220415)
      ·
        refine ⟨4878891641034764427330623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252594427356509618220415 4878891641034764427330623)
        ·
          refine ⟨7318337461552146640995935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878891641034764427330623 7318337461552146640995935)
          ·
            refine ⟨10977506192328219961493903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318337461552146640995935 10977506192328219961493903)
            ·
              refine ⟨16466259288492329942240855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10977506192328219961493903 16466259288492329942240855)
              ·
                refine ⟨24699388932738494913361283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16466259288492329942240855 24699388932738494913361283)
                ·
                  refine ⟨37049083399107742370041925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24699388932738494913361283 37049083399107742370041925)
                  ·
                    refine ⟨6946703137332701694382861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37049083399107742370041925 6946703137332701694382861)
                    ·
                      refine ⟨2605013676499763135393573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6946703137332701694382861 2605013676499763135393573)
                      ·
                        rfl

theorem cell23_5073246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5073246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073246 prefixEnd_5073246 := by exact prefixLift 5073246
  have htrace : WordTrace (prefixWord ++ tailWord_5073246) baseStart_5073246 baseEnd_5073246 := by
    simpa [prefixWord, tailWord_5073246, baseEnd_5073246] using wordTrace_append hprefix tailTrace_5073246
  have hstable : (prefixWord ++ tailWord_5073246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073246).length < 2 ^ (prefixWord ++ tailWord_5073246).sum := by decide
  have hdescent : baseEnd_5073246 < baseStart_5073246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073265 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 7, 2, 2]
def baseStart_5073265 : Nat := 118140960795 + 5073265 * 2 ^ 59
def prefixEnd_5073265 : Nat := 4983230072969 + 3 ^ 40 * 5073265 * 2
def baseEnd_5073265 : Nat := 2605023432632198561055985

theorem tailTrace_5073265 : CollatzResearch.WordTrace tailWord_5073265 prefixEnd_5073265 2605023432632198561055985 := by
  unfold tailWord_5073265
  simp only [CollatzResearch.WordTrace]
  refine ⟨185037175965434824525925249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123358117310289883017283499 185037175965434824525925249)
  ·
    refine ⟨138777881974076118394443937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185037175965434824525925249 138777881974076118394443937)
    ·
      refine ⟨104083411480557088795832953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138777881974076118394443937 104083411480557088795832953)
      ·
        refine ⟨78062558610417816596874715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104083411480557088795832953 78062558610417816596874715)
        ·
          refine ⟨117093837915626724895312073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78062558610417816596874715 117093837915626724895312073)
          ·
            refine ⟨87820378436720043671484055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117093837915626724895312073 87820378436720043671484055)
            ·
              refine ⟨131730567655080065507226083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87820378436720043671484055 131730567655080065507226083)
              ·
                refine ⟨197595851482620098260839125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131730567655080065507226083 197595851482620098260839125)
                ·
                  refine ⟨4631152769123908552988417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197595851482620098260839125 4631152769123908552988417)
                  ·
                    refine ⟨3473364576842931414741313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631152769123908552988417 3473364576842931414741313)
                    ·
                      refine ⟨2605023432632198561055985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473364576842931414741313 2605023432632198561055985)
                      ·
                        rfl

theorem cell23_5073265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_5073265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073265 prefixEnd_5073265 := by exact prefixLift 5073265
  have htrace : WordTrace (prefixWord ++ tailWord_5073265) baseStart_5073265 baseEnd_5073265 := by
    simpa [prefixWord, tailWord_5073265, baseEnd_5073265] using wordTrace_append hprefix tailTrace_5073265
  have hstable : (prefixWord ++ tailWord_5073265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073265).length < 2 ^ (prefixWord ++ tailWord_5073265).sum := by decide
  have hdescent : baseEnd_5073265 < baseStart_5073265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073275 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 2, 4]
def baseStart_5073275 : Nat := 118140960795 + 5073275 * 2 ^ 59
def prefixEnd_5073275 : Nat := 4983230072969 + 3 ^ 40 * 5073275 * 2
def baseEnd_5073275 : Nat := 868342855812914507310313

theorem tailTrace_5073275 : CollatzResearch.WordTrace tailWord_5073275 prefixEnd_5073275 868342855812914507310313 := by
  unfold tailWord_5073275
  simp only [CollatzResearch.WordTrace]
  refine ⟨185037540695398596233789279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123358360463599064155859519 185037540695398596233789279)
  ·
    refine ⟨277556311043097894350683919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185037540695398596233789279 277556311043097894350683919)
    ·
      refine ⟨416334466564646841526025879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277556311043097894350683919 416334466564646841526025879)
      ·
        refine ⟨624501699846970262289038819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416334466564646841526025879 624501699846970262289038819)
        ·
          refine ⟨936752549770455393433558229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624501699846970262289038819 936752549770455393433558229)
          ·
            refine ⟨21955137885245048283599021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 936752549770455393433558229 21955137885245048283599021)
            ·
              refine ⟨8233176706966893106349633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21955137885245048283599021 8233176706966893106349633)
              ·
                refine ⟨6174882530225169829762225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8233176706966893106349633 6174882530225169829762225)
                ·
                  refine ⟨4631161897668877372321669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6174882530225169829762225 4631161897668877372321669)
                  ·
                    refine ⟨868342855812914507310313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631161897668877372321669 868342855812914507310313)
                    ·
                      rfl

theorem cell23_5073275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 4].length) (baseStart_5073275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073275 prefixEnd_5073275 := by exact prefixLift 5073275
  have htrace : WordTrace (prefixWord ++ tailWord_5073275) baseStart_5073275 baseEnd_5073275 := by
    simpa [prefixWord, tailWord_5073275, baseEnd_5073275] using wordTrace_append hprefix tailTrace_5073275
  have hstable : (prefixWord ++ tailWord_5073275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073275).length < 2 ^ (prefixWord ++ tailWord_5073275).sum := by decide
  have hdescent : baseEnd_5073275 < baseStart_5073275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073292 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_5073292 : Nat := 118140960795 + 5073292 * 2 ^ 59
def prefixEnd_5073292 : Nat := 4983230072969 + 3 ^ 40 * 5073292 * 2
def baseEnd_5073292 : Nat := 868345765536623318472787

theorem tailTrace_5073292 : CollatzResearch.WordTrace tailWord_5073292 prefixEnd_5073292 868345765536623318472787 := by
  unfold tailWord_5073292
  simp only [CollatzResearch.WordTrace]
  refine ⟨92519080368168504068579065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123358773824224672091438753 92519080368168504068579065)
  ·
    refine ⟨69389310276126378051434299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92519080368168504068579065 69389310276126378051434299)
    ·
      refine ⟨104083965414189567077151449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69389310276126378051434299 104083965414189567077151449)
      ·
        refine ⟨78062974060642175307863587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104083965414189567077151449 78062974060642175307863587)
        ·
          refine ⟨117094461090963262961795381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78062974060642175307863587 117094461090963262961795381)
          ·
            refine ⟨10977605727277805902668317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117094461090963262961795381 10977605727277805902668317)
            ·
              refine ⟨4116602147729177213500619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10977605727277805902668317 4116602147729177213500619)
              ·
                refine ⟨6174903221593765820250929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116602147729177213500619 6174903221593765820250929)
                ·
                  refine ⟨4631177416195324365188197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6174903221593765820250929 4631177416195324365188197)
                  ·
                    refine ⟨868345765536623318472787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631177416195324365188197 868345765536623318472787)
                    ·
                      rfl

theorem cell23_5073292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_5073292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073292 prefixEnd_5073292 := by exact prefixLift 5073292
  have htrace : WordTrace (prefixWord ++ tailWord_5073292) baseStart_5073292 baseEnd_5073292 := by
    simpa [prefixWord, tailWord_5073292, baseEnd_5073292] using wordTrace_append hprefix tailTrace_5073292
  have hstable : (prefixWord ++ tailWord_5073292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073292).length < 2 ^ (prefixWord ++ tailWord_5073292).sum := by decide
  have hdescent : baseEnd_5073292 < baseStart_5073292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073315 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 3]
def baseStart_5073315 : Nat := 118140960795 + 5073315 * 2 ^ 59
def prefixEnd_5073315 : Nat := 4983230072969 + 3 ^ 40 * 5073315 * 2
def baseEnd_5073315 : Nat := 2605049106664923365430755

theorem tailTrace_5073315 : CollatzResearch.WordTrace tailWord_5073315 prefixEnd_5073315 2605049106664923365430755 := by
  unfold tailWord_5073315
  simp only [CollatzResearch.WordTrace]
  refine ⟨185038999615253683065245399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123359333076835788710163599 185038999615253683065245399)
  ·
    refine ⟨277558499422880524597868099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185038999615253683065245399 277558499422880524597868099)
    ·
      refine ⟨416337749134320786896802149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277558499422880524597868099 416337749134320786896802149)
      ·
        refine ⟨78063327962685147543150403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 416337749134320786896802149 78063327962685147543150403)
        ·
          refine ⟨117094991944027721314725605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78063327962685147543150403 117094991944027721314725605)
          ·
            refine ⟨21955310989505197746511051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117094991944027721314725605 21955310989505197746511051)
            ·
              refine ⟨32932966484257796619766577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21955310989505197746511051 32932966484257796619766577)
              ·
                refine ⟨24699724863193347464824933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32932966484257796619766577 24699724863193347464824933)
                ·
                  refine ⟨4631198411848752649654675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24699724863193347464824933 4631198411848752649654675)
                  ·
                    refine ⟨6946797617773128974482013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4631198411848752649654675 6946797617773128974482013)
                    ·
                      refine ⟨2605049106664923365430755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6946797617773128974482013 2605049106664923365430755)
                      ·
                        rfl

theorem cell23_5073315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_5073315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073315 prefixEnd_5073315 := by exact prefixLift 5073315
  have htrace : WordTrace (prefixWord ++ tailWord_5073315) baseStart_5073315 baseEnd_5073315 := by
    simpa [prefixWord, tailWord_5073315, baseEnd_5073315] using wordTrace_append hprefix tailTrace_5073315
  have hstable : (prefixWord ++ tailWord_5073315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073315).length < 2 ^ (prefixWord ++ tailWord_5073315).sum := by decide
  have hdescent : baseEnd_5073315 < baseStart_5073315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073321 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_5073321 : Nat := 118140960795 + 5073321 * 2 ^ 59
def prefixEnd_5073321 : Nat := 4983230072969 + 3 ^ 40 * 5073321 * 2
def baseEnd_5073321 : Nat := 2605052187548850341955727

theorem tailTrace_5073321 : CollatzResearch.WordTrace tailWord_5073321 prefixEnd_5073321 2605052187548850341955727 := by
  unfold tailWord_5073321
  simp only [CollatzResearch.WordTrace]
  refine ⟨185039218453231946089963817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123359478968821297393309211 185039218453231946089963817)
  ·
    refine ⟨138779413839923959567472863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185039218453231946089963817 138779413839923959567472863)
    ·
      refine ⟨208169120759885939351209295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138779413839923959567472863 208169120759885939351209295)
      ·
        refine ⟨312253681139828909026813943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208169120759885939351209295 312253681139828909026813943)
        ·
          refine ⟨468380521709743363540220915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312253681139828909026813943 468380521709743363540220915)
          ·
            refine ⟨702570782564615045310331373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468380521709743363540220915 702570782564615045310331373)
            ·
              refine ⟨263464043461730641991374265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 702570782564615045310331373 263464043461730641991374265)
              ·
                refine ⟨197598032596297981493530699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263464043461730641991374265 197598032596297981493530699)
                ·
                  refine ⟨296397048894446972240296049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197598032596297981493530699 296397048894446972240296049)
                  ·
                    refine ⟨222297786670835229180222037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 296397048894446972240296049 222297786670835229180222037)
                    ·
                      refine ⟨2605052187548850341955727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 222297786670835229180222037 2605052187548850341955727)
                      ·
                        rfl

theorem cell23_5073321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_5073321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073321 prefixEnd_5073321 := by exact prefixLift 5073321
  have htrace : WordTrace (prefixWord ++ tailWord_5073321) baseStart_5073321 baseEnd_5073321 := by
    simpa [prefixWord, tailWord_5073321, baseEnd_5073321] using wordTrace_append hprefix tailTrace_5073321
  have hstable : (prefixWord ++ tailWord_5073321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073321).length < 2 ^ (prefixWord ++ tailWord_5073321).sum := by decide
  have hdescent : baseEnd_5073321 < baseStart_5073321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073333 : List Nat := [1, 3, 3, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_5073333 : Nat := 118140960795 + 5073333 * 2 ^ 59
def prefixEnd_5073333 : Nat := 4983230072969 + 3 ^ 40 * 5073333 * 2
def baseEnd_5073333 : Nat := 2605058349316704295005673

theorem tailTrace_5073333 : CollatzResearch.WordTrace tailWord_5073333 prefixEnd_5073333 2605058349316704295005673 := by
  unfold tailWord_5073333
  simp only [CollatzResearch.WordTrace]
  refine ⟨185039656129188472139400653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123359770752792314759600435 185039656129188472139400653)
  ·
    refine ⟨69389871048445677052275245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185039656129188472139400653 69389871048445677052275245)
    ·
      refine ⟨26021201643167128894603217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69389871048445677052275245 26021201643167128894603217)
      ·
        refine ⟨19515901232375346670952413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26021201643167128894603217 19515901232375346670952413)
        ·
          refine ⟨7318462962140755001607155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19515901232375346670952413 7318462962140755001607155)
          ·
            refine ⟨10977694443211132502410733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318462962140755001607155 10977694443211132502410733)
            ·
              refine ⟨4116635416204174688404025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10977694443211132502410733 4116635416204174688404025)
              ·
                refine ⟨3087476562153131016303019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116635416204174688404025 3087476562153131016303019)
                ·
                  refine ⟨4631214843229696524454529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087476562153131016303019 4631214843229696524454529)
                  ·
                    refine ⟨3473411132422272393340897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631214843229696524454529 3473411132422272393340897)
                    ·
                      refine ⟨2605058349316704295005673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473411132422272393340897 2605058349316704295005673)
                      ·
                        rfl

theorem cell23_5073333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_5073333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073333 prefixEnd_5073333 := by exact prefixLift 5073333
  have htrace : WordTrace (prefixWord ++ tailWord_5073333) baseStart_5073333 baseEnd_5073333 := by
    simpa [prefixWord, tailWord_5073333, baseEnd_5073333] using wordTrace_append hprefix tailTrace_5073333
  have hstable : (prefixWord ++ tailWord_5073333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073333).length < 2 ^ (prefixWord ++ tailWord_5073333).sum := by decide
  have hdescent : baseEnd_5073333 < baseStart_5073333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073355 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 1, 4, 2]
def baseStart_5073355 : Nat := 118140960795 + 5073355 * 2 ^ 59
def prefixEnd_5073355 : Nat := 4983230072969 + 3 ^ 40 * 5073355 * 2
def baseEnd_5073355 : Nat := 2605069645891103208930571

theorem tailTrace_5073355 : CollatzResearch.WordTrace tailWord_5073355 prefixEnd_5073355 2605069645891103208930571 := by
  unfold tailWord_5073355
  simp only [CollatzResearch.WordTrace]
  refine ⟨185040458535108769896701519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123360305690072513264467679 185040458535108769896701519)
  ·
    refine ⟨277560687802663154845052279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185040458535108769896701519 277560687802663154845052279)
    ·
      refine ⟨416341031703994732267578419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277560687802663154845052279 416341031703994732267578419)
      ·
        refine ⟨624511547555992098401367629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416341031703994732267578419 624511547555992098401367629)
        ·
          refine ⟨234191830333497036900512861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 624511547555992098401367629 234191830333497036900512861)
          ·
            refine ⟨87821936375061388837692323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234191830333497036900512861 87821936375061388837692323)
            ·
              refine ⟨131732904562592083256538485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87821936375061388837692323 131732904562592083256538485)
              ·
                refine ⟨12349959802743007805300483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131732904562592083256538485 12349959802743007805300483)
                ·
                  refine ⟨18524939704114511707950725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12349959802743007805300483 18524939704114511707950725)
                  ·
                    refine ⟨3473426194521470945240761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18524939704114511707950725 3473426194521470945240761)
                    ·
                      refine ⟨2605069645891103208930571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473426194521470945240761 2605069645891103208930571)
                      ·
                        rfl

theorem cell23_5073355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4, 2].length) (baseStart_5073355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073355 prefixEnd_5073355 := by exact prefixLift 5073355
  have htrace : WordTrace (prefixWord ++ tailWord_5073355) baseStart_5073355 baseEnd_5073355 := by
    simpa [prefixWord, tailWord_5073355, baseEnd_5073355] using wordTrace_append hprefix tailTrace_5073355
  have hstable : (prefixWord ++ tailWord_5073355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073355).length < 2 ^ (prefixWord ++ tailWord_5073355).sum := by decide
  have hdescent : baseEnd_5073355 < baseStart_5073355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073368 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_5073368 : Nat := 118140960795 + 5073368 * 2 ^ 59
def prefixEnd_5073368 : Nat := 4983230072969 + 3 ^ 40 * 5073368 * 2
def baseEnd_5073368 : Nat := 2605076321139611658068011

theorem tailTrace_5073368 : CollatzResearch.WordTrace tailWord_5073368 prefixEnd_5073368 2605076321139611658068011 := by
  unfold tailWord_5073368
  simp only [CollatzResearch.WordTrace]
  refine ⟨92520466342030836558462379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123360621789374448744616505 92520466342030836558462379)
  ·
    refine ⟨138780699513046254837693569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92520466342030836558462379 138780699513046254837693569)
    ·
      refine ⟨104085524634784691128270177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138780699513046254837693569 104085524634784691128270177)
      ·
        refine ⟨78064143476088518346202633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104085524634784691128270177 78064143476088518346202633)
        ·
          refine ⟨58548107607066388759651975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78064143476088518346202633 58548107607066388759651975)
          ·
            refine ⟨87822161410599583139477963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58548107607066388759651975 87822161410599583139477963)
            ·
              refine ⟨131733242115899374709216945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87822161410599583139477963 131733242115899374709216945)
              ·
                refine ⟨98799931586924531031912709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131733242115899374709216945 98799931586924531031912709)
                ·
                  refine ⟨18524987172548349568483633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98799931586924531031912709 18524987172548349568483633)
                  ·
                    refine ⟨13893740379411262176362725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18524987172548349568483633 13893740379411262176362725)
                    ·
                      refine ⟨2605076321139611658068011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13893740379411262176362725 2605076321139611658068011)
                      ·
                        rfl

theorem cell23_5073368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_5073368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073368 prefixEnd_5073368 := by exact prefixLift 5073368
  have htrace : WordTrace (prefixWord ++ tailWord_5073368) baseStart_5073368 baseEnd_5073368 := by
    simpa [prefixWord, tailWord_5073368, baseEnd_5073368] using wordTrace_append hprefix tailTrace_5073368
  have hstable : (prefixWord ++ tailWord_5073368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073368).length < 2 ^ (prefixWord ++ tailWord_5073368).sum := by decide
  have hdescent : baseEnd_5073368 < baseStart_5073368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073395 : List Nat := [1, 1, 1, 2, 2, 2, 5, 4, 5]
def baseStart_5073395 : Nat := 118140960795 + 5073395 * 2 ^ 59
def prefixEnd_5073395 : Nat := 4983230072969 + 3 ^ 40 * 5073395 * 2
def baseEnd_5073395 : Nat := 289454465013031450270043

theorem tailTrace_5073395 : CollatzResearch.WordTrace tailWord_5073395 prefixEnd_5073395 289454465013031450270043 := by
  unfold tailWord_5073395
  simp only [CollatzResearch.WordTrace]
  refine ⟨185041917454963856728157639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123361278303309237818771759 185041917454963856728157639)
  ·
    refine ⟨277562876182445785092236459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185041917454963856728157639 277562876182445785092236459)
    ·
      refine ⟨416344314273668677638354689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277562876182445785092236459 416344314273668677638354689)
      ·
        refine ⟨312258235705251508228766017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416344314273668677638354689 312258235705251508228766017)
        ·
          refine ⟨234193676778938631171574513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312258235705251508228766017 234193676778938631171574513)
          ·
            refine ⟨175645257584203973378680885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234193676778938631171574513 175645257584203973378680885)
            ·
              refine ⟨16466742898519122504251333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175645257584203973378680885 16466742898519122504251333)
              ·
                refine ⟨3087514293472335469547125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16466742898519122504251333 3087514293472335469547125)
                ·
                  refine ⟨289454465013031450270043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3087514293472335469547125 289454465013031450270043)
                  ·
                    rfl

theorem cell23_5073395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 5].length) (baseStart_5073395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073395 prefixEnd_5073395 := by exact prefixLift 5073395
  have htrace : WordTrace (prefixWord ++ tailWord_5073395) baseStart_5073395 baseEnd_5073395 := by
    simpa [prefixWord, tailWord_5073395, baseEnd_5073395] using wordTrace_append hprefix tailTrace_5073395
  have hstable : (prefixWord ++ tailWord_5073395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073395).length < 2 ^ (prefixWord ++ tailWord_5073395).sum := by decide
  have hdescent : baseEnd_5073395 < baseStart_5073395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073405 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_5073405 : Nat := 118140960795 + 5073405 * 2 ^ 59
def prefixEnd_5073405 : Nat := 4983230072969 + 3 ^ 40 * 5073405 * 2
def baseEnd_5073405 : Nat := 2605095319923828013305341

theorem tailTrace_5073405 : CollatzResearch.WordTrace tailWord_5073405 prefixEnd_5073405 2605095319923828013305341 := by
  unfold tailWord_5073405
  simp only [CollatzResearch.WordTrace]
  refine ⟨185042282184927628436021669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123361521456618418957347779 185042282184927628436021669)
  ·
    refine ⟨34695427909673930331754063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185042282184927628436021669 34695427909673930331754063)
    ·
      refine ⟨52043141864510895497631095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34695427909673930331754063 52043141864510895497631095)
      ·
        refine ⟨78064712796766343246446643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52043141864510895497631095 78064712796766343246446643)
        ·
          refine ⟨117097069195149514869669965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78064712796766343246446643 117097069195149514869669965)
          ·
            refine ⟨43911400948181068076126237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117097069195149514869669965 43911400948181068076126237)
            ·
              refine ⟨16466775355567900528547339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43911400948181068076126237 16466775355567900528547339)
              ·
                refine ⟨24700163033351850792821009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16466775355567900528547339 24700163033351850792821009)
                ·
                  refine ⟨18525122275013888094615757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24700163033351850792821009 18525122275013888094615757)
                  ·
                    refine ⟨6946920853130208035480909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18525122275013888094615757 6946920853130208035480909)
                    ·
                      refine ⟨2605095319923828013305341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6946920853130208035480909 2605095319923828013305341)
                      ·
                        rfl

theorem cell23_5073405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_5073405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073405 prefixEnd_5073405 := by exact prefixLift 5073405
  have htrace : WordTrace (prefixWord ++ tailWord_5073405) baseStart_5073405 baseEnd_5073405 := by
    simpa [prefixWord, tailWord_5073405, baseEnd_5073405] using wordTrace_append hprefix tailTrace_5073405
  have hstable : (prefixWord ++ tailWord_5073405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073405).length < 2 ^ (prefixWord ++ tailWord_5073405).sum := by decide
  have hdescent : baseEnd_5073405 < baseStart_5073405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073445 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_5073445 : Nat := 118140960795 + 5073445 * 2 ^ 59
def prefixEnd_5073445 : Nat := 4983230072969 + 3 ^ 40 * 5073445 * 2
def baseEnd_5073445 : Nat := 2605115859150007856805157

theorem tailTrace_5073445 : CollatzResearch.WordTrace tailWord_5073445 prefixEnd_5073445 2605115859150007856805157 := by
  unfold tailWord_5073445
  simp only [CollatzResearch.WordTrace]
  refine ⟨185043741104782715267477789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123362494069855143511651859 185043741104782715267477789)
  ·
    refine ⟨69391402914293518225304171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185043741104782715267477789 69391402914293518225304171)
    ·
      refine ⟨104087104371440277337956257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69391402914293518225304171 104087104371440277337956257)
      ·
        refine ⟨78065328278580208003467193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104087104371440277337956257 78065328278580208003467193)
        ·
          refine ⟨58548996208935156002600395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78065328278580208003467193 58548996208935156002600395)
          ·
            refine ⟨87823494313402734003900593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58548996208935156002600395 87823494313402734003900593)
            ·
              refine ⟨65867620735052050502925445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87823494313402734003900593 65867620735052050502925445)
              ·
                refine ⟨12350178887822259469298521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65867620735052050502925445 12350178887822259469298521)
                ·
                  refine ⟨9262634165866694601973891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12350178887822259469298521 9262634165866694601973891)
                  ·
                    refine ⟨13893951248800041902960837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9262634165866694601973891 13893951248800041902960837)
                    ·
                      refine ⟨2605115859150007856805157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13893951248800041902960837 2605115859150007856805157)
                      ·
                        rfl

theorem cell23_5073445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_5073445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073445 prefixEnd_5073445 := by exact prefixLift 5073445
  have htrace : WordTrace (prefixWord ++ tailWord_5073445) baseStart_5073445 baseEnd_5073445 := by
    simpa [prefixWord, tailWord_5073445, baseEnd_5073445] using wordTrace_append hprefix tailTrace_5073445
  have hstable : (prefixWord ++ tailWord_5073445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073445).length < 2 ^ (prefixWord ++ tailWord_5073445).sum := by decide
  have hdescent : baseEnd_5073445 < baseStart_5073445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073462 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5073462 : Nat := 118140960795 + 5073462 * 2 ^ 59
def prefixEnd_5073462 : Nat := 4983230072969 + 3 ^ 40 * 5073462 * 2
def baseEnd_5073462 : Nat := 2605124588321134290292579

theorem tailTrace_5073462 : CollatzResearch.WordTrace tailWord_5073462 prefixEnd_5073462 2605124588321134290292579 := by
  unfold tailWord_5073462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11565272571607570448177915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123362907430480751447231093 11565272571607570448177915)
  ·
    refine ⟨17347908857411355672266873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11565272571607570448177915 17347908857411355672266873)
    ·
      refine ⟨13010931643058516754200155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17347908857411355672266873 13010931643058516754200155)
      ·
        refine ⟨19516397464587775131300233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13010931643058516754200155 19516397464587775131300233)
        ·
          refine ⟨14637298098440831348475175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19516397464587775131300233 14637298098440831348475175)
          ·
            refine ⟨21955947147661247022712763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14637298098440831348475175 21955947147661247022712763)
            ·
              refine ⟨32933920721491870534069145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21955947147661247022712763 32933920721491870534069145)
              ·
                refine ⟨24700440541118902900551859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32933920721491870534069145 24700440541118902900551859)
                ·
                  refine ⟨37050660811678354350827789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24700440541118902900551859 37050660811678354350827789)
                  ·
                    refine ⟨13893997804379382881560421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37050660811678354350827789 13893997804379382881560421)
                    ·
                      refine ⟨2605124588321134290292579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13893997804379382881560421 2605124588321134290292579)
                      ·
                        rfl

theorem cell23_5073462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5073462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073462 prefixEnd_5073462 := by exact prefixLift 5073462
  have htrace : WordTrace (prefixWord ++ tailWord_5073462) baseStart_5073462 baseEnd_5073462 := by
    simpa [prefixWord, tailWord_5073462, baseEnd_5073462] using wordTrace_append hprefix tailTrace_5073462
  have hstable : (prefixWord ++ tailWord_5073462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073462).length < 2 ^ (prefixWord ++ tailWord_5073462).sum := by decide
  have hdescent : baseEnd_5073462 < baseStart_5073462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073465 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5073465 : Nat := 118140960795 + 5073465 * 2 ^ 59
def prefixEnd_5073465 : Nat := 4983230072969 + 3 ^ 40 * 5073465 * 2
def baseEnd_5073465 : Nat := 2605126128763097778555065

theorem tailTrace_5073465 : CollatzResearch.WordTrace tailWord_5073465 prefixEnd_5073465 2605126128763097778555065 := by
  unfold tailWord_5073465
  simp only [CollatzResearch.WordTrace]
  refine ⟨185044470564710258683205849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123362980376473505788803899 185044470564710258683205849)
  ·
    refine ⟨138783352923532694012404387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185044470564710258683205849 138783352923532694012404387)
    ·
      refine ⟨208175029385299041018606581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138783352923532694012404387 208175029385299041018606581)
      ·
        refine ⟨19516409004871785095494367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208175029385299041018606581 19516409004871785095494367)
        ·
          refine ⟨29274613507307677643241551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19516409004871785095494367 29274613507307677643241551)
          ·
            refine ⟨43911920260961516464862327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29274613507307677643241551 43911920260961516464862327)
            ·
              refine ⟨65867880391442274697293491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43911920260961516464862327 65867880391442274697293491)
              ·
                refine ⟨98801820587163412045940237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65867880391442274697293491 98801820587163412045940237)
                ·
                  refine ⟨37050682720186279517227589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98801820587163412045940237 37050682720186279517227589)
                  ·
                    refine ⟨6947003010034927409480173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37050682720186279517227589 6947003010034927409480173)
                    ·
                      refine ⟨2605126128763097778555065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6947003010034927409480173 2605126128763097778555065)
                      ·
                        rfl

theorem cell23_5073465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5073465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073465 prefixEnd_5073465 := by exact prefixLift 5073465
  have htrace : WordTrace (prefixWord ++ tailWord_5073465) baseStart_5073465 baseEnd_5073465 := by
    simpa [prefixWord, tailWord_5073465, baseEnd_5073465] using wordTrace_append hprefix tailTrace_5073465
  have hstable : (prefixWord ++ tailWord_5073465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073465).length < 2 ^ (prefixWord ++ tailWord_5073465).sum := by decide
  have hdescent : baseEnd_5073465 < baseStart_5073465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073488 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_5073488 : Nat := 118140960795 + 5073488 * 2 ^ 59
def prefixEnd_5073488 : Nat := 4983230072969 + 3 ^ 40 * 5073488 * 2
def baseEnd_5073488 : Nat := 2605137938818151188567459

theorem tailTrace_5073488 : CollatzResearch.WordTrace tailWord_5073488 prefixEnd_5073488 2605137938818151188567459 := by
  unfold tailWord_5073488
  simp only [CollatzResearch.WordTrace]
  refine ⟨92522654721813466805646559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123363539629084622407528745 92522654721813466805646559)
  ·
    refine ⟨138783982082720200208469839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92522654721813466805646559 138783982082720200208469839)
    ·
      refine ⟨208175973124080300312704759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138783982082720200208469839 208175973124080300312704759)
      ·
        refine ⟨312263959686120450469057139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208175973124080300312704759 312263959686120450469057139)
        ·
          refine ⟨468395939529180675703585709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312263959686120450469057139 468395939529180675703585709)
          ·
            refine ⟨175648477323442753388844641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468395939529180675703585709 175648477323442753388844641)
            ·
              refine ⟨131736357992582065041633481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175648477323442753388844641 131736357992582065041633481)
              ·
                refine ⟨98802268494436548781225111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131736357992582065041633481 98802268494436548781225111)
                ·
                  refine ⟨148203402741654823171837667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98802268494436548781225111 148203402741654823171837667)
                  ·
                    refine ⟨222305104112482234757756501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148203402741654823171837667 222305104112482234757756501)
                    ·
                      refine ⟨2605137938818151188567459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 222305104112482234757756501 2605137938818151188567459)
                      ·
                        rfl

theorem cell23_5073488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_5073488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073488 prefixEnd_5073488 := by exact prefixLift 5073488
  have htrace : WordTrace (prefixWord ++ tailWord_5073488) baseStart_5073488 baseEnd_5073488 := by
    simpa [prefixWord, tailWord_5073488, baseEnd_5073488] using wordTrace_append hprefix tailTrace_5073488
  have hstable : (prefixWord ++ tailWord_5073488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073488).length < 2 ^ (prefixWord ++ tailWord_5073488).sum := by decide
  have hdescent : baseEnd_5073488 < baseStart_5073488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073489 : List Nat := [1, 2, 2, 1, 3, 3, 3, 3, 1, 4]
def baseStart_5073489 : Nat := 118140960795 + 5073489 * 2 ^ 59
def prefixEnd_5073489 : Nat := 4983230072969 + 3 ^ 40 * 5073489 * 2
def baseEnd_5073489 : Nat := 868379484099601894884985

theorem tailTrace_5073489 : CollatzResearch.WordTrace tailWord_5073489 prefixEnd_5073489 868379484099601894884985 := by
  unfold tailWord_5073489
  simp only [CollatzResearch.WordTrace]
  refine ⟨185045345916623310782079521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123363563944415540521386347 185045345916623310782079521)
  ·
    refine ⟨138784009437467483086559641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185045345916623310782079521 138784009437467483086559641)
    ·
      refine ⟨104088007078100612314919731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138784009437467483086559641 104088007078100612314919731)
      ·
        refine ⟨156132010617150918472379597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104088007078100612314919731 156132010617150918472379597)
        ·
          refine ⟨58549503981431594427142349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156132010617150918472379597 58549503981431594427142349)
          ·
            refine ⟨21956063993036847910178381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58549503981431594427142349 21956063993036847910178381)
            ·
              refine ⟨8233523997388817966316893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21956063993036847910178381 8233523997388817966316893)
              ·
                refine ⟨3087571499020806737368835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8233523997388817966316893 3087571499020806737368835)
                ·
                  refine ⟨4631357248531210106053253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087571499020806737368835 4631357248531210106053253)
                  ·
                    refine ⟨868379484099601894884985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631357248531210106053253 868379484099601894884985)
                    ·
                      rfl

theorem cell23_5073489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_5073489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073489 prefixEnd_5073489 := by exact prefixLift 5073489
  have htrace : WordTrace (prefixWord ++ tailWord_5073489) baseStart_5073489 baseEnd_5073489 := by
    simpa [prefixWord, tailWord_5073489, baseEnd_5073489] using wordTrace_append hprefix tailTrace_5073489
  have hstable : (prefixWord ++ tailWord_5073489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073489).length < 2 ^ (prefixWord ++ tailWord_5073489).sum := by decide
  have hdescent : baseEnd_5073489 < baseStart_5073489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073532 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_5073532 : Nat := 118140960795 + 5073532 * 2 ^ 59
def prefixEnd_5073532 : Nat := 4983230072969 + 3 ^ 40 * 5073532 * 2
def baseEnd_5073532 : Nat := 868386843988983005472419

theorem tailTrace_5073532 : CollatzResearch.WordTrace tailWord_5073532 prefixEnd_5073532 868386843988983005472419 := by
  unfold tailWord_5073532
  simp only [CollatzResearch.WordTrace]
  refine ⟨92523457127733764562947425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123364609503645019417263233 92523457127733764562947425)
  ·
    refine ⟨69392592845800323422210569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92523457127733764562947425 69392592845800323422210569)
    ·
      refine ⟨52044444634350242566657927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69392592845800323422210569 52044444634350242566657927)
      ·
        refine ⟨78066666951525363849986891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52044444634350242566657927 78066666951525363849986891)
        ·
          refine ⟨117100000427288045774980337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78066666951525363849986891 117100000427288045774980337)
          ·
            refine ⟨87825000320466034331235253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117100000427288045774980337 87825000320466034331235253)
            ·
              refine ⟨8233593780043690718553305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87825000320466034331235253 8233593780043690718553305)
              ·
                refine ⟨6175195335032768038914979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8233593780043690718553305 6175195335032768038914979)
                ·
                  refine ⟨9262793002549152058372469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6175195335032768038914979 9262793002549152058372469)
                  ·
                    refine ⟨868386843988983005472419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9262793002549152058372469 868386843988983005472419)
                    ·
                      rfl

theorem cell23_5073532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_5073532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073532 prefixEnd_5073532 := by exact prefixLift 5073532
  have htrace : WordTrace (prefixWord ++ tailWord_5073532) baseStart_5073532 baseEnd_5073532 := by
    simpa [prefixWord, tailWord_5073532, baseEnd_5073532] using wordTrace_append hprefix tailTrace_5073532
  have hstable : (prefixWord ++ tailWord_5073532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073532).length < 2 ^ (prefixWord ++ tailWord_5073532).sum := by decide
  have hdescent : baseEnd_5073532 < baseStart_5073532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073556 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_5073556 : Nat := 118140960795 + 5073556 * 2 ^ 59
def prefixEnd_5073556 : Nat := 4983230072969 + 3 ^ 40 * 5073556 * 2
def baseEnd_5073556 : Nat := 2605172855502656922517147

theorem tailTrace_5073556 : CollatzResearch.WordTrace tailWord_5073556 prefixEnd_5073556 2605172855502656922517147 := by
  unfold tailWord_5073556
  simp only [CollatzResearch.WordTrace]
  refine ⟨92523894803690290612384261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123365193071587054149845681 92523894803690290612384261)
  ·
    refine ⟨17348230275691929489822049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92523894803690290612384261 17348230275691929489822049)
    ·
      refine ⟨13011172706768947117366537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17348230275691929489822049 13011172706768947117366537)
      ·
        refine ⟨9758379530076710338024903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13011172706768947117366537 9758379530076710338024903)
        ·
          refine ⟨14637569295115065507037355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9758379530076710338024903 14637569295115065507037355)
          ·
            refine ⟨21956353942672598260556033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14637569295115065507037355 21956353942672598260556033)
            ·
              refine ⟨16467265457004448695417025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21956353942672598260556033 16467265457004448695417025)
              ·
                refine ⟨12350449092753336521562769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16467265457004448695417025 12350449092753336521562769)
                ·
                  refine ⟨9262836819565002391172077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12350449092753336521562769 9262836819565002391172077)
                  ·
                    refine ⟨3473563807336875896689529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9262836819565002391172077 3473563807336875896689529)
                    ·
                      refine ⟨2605172855502656922517147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473563807336875896689529 2605172855502656922517147)
                      ·
                        rfl

theorem cell23_5073556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_5073556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073556 prefixEnd_5073556 := by exact prefixLift 5073556
  have htrace : WordTrace (prefixWord ++ tailWord_5073556) baseStart_5073556 baseEnd_5073556 := by
    simpa [prefixWord, tailWord_5073556, baseEnd_5073556] using wordTrace_append hprefix tailTrace_5073556
  have hstable : (prefixWord ++ tailWord_5073556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073556).length < 2 ^ (prefixWord ++ tailWord_5073556).sum := by decide
  have hdescent : baseEnd_5073556 < baseStart_5073556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073565 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5073565 : Nat := 118140960795 + 5073565 * 2 ^ 59
def prefixEnd_5073565 : Nat := 4983230072969 + 3 ^ 40 * 5073565 * 2
def baseEnd_5073565 : Nat := 2605177476828547387304605

theorem tailTrace_5073565 : CollatzResearch.WordTrace tailWord_5073565 prefixEnd_5073565 2605177476828547387304605 := by
  unfold tailWord_5073565
  simp only [CollatzResearch.WordTrace]
  refine ⟨185048117864347975761846149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123365411909565317174564099 185048117864347975761846149)
  ·
    refine ⟨34696522099565245455346153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185048117864347975761846149 34696522099565245455346153)
    ·
      refine ⟨26022391574673934091509615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34696522099565245455346153 26022391574673934091509615)
      ·
        refine ⟨39033587362010901137264423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26022391574673934091509615 39033587362010901137264423)
        ·
          refine ⟨58550381043016351705896635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39033587362010901137264423 58550381043016351705896635)
          ·
            refine ⟨87825571564524527558844953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58550381043016351705896635 87825571564524527558844953)
            ·
              refine ⟨65869178673393395669133715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87825571564524527558844953 65869178673393395669133715)
              ·
                refine ⟨98803768010090093503700573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65869178673393395669133715 98803768010090093503700573)
                ·
                  refine ⟨37051413003783785063887715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98803768010090093503700573 37051413003783785063887715)
                  ·
                    refine ⟨55577119505675677595831573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37051413003783785063887715 55577119505675677595831573)
                    ·
                      refine ⟨2605177476828547387304605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55577119505675677595831573 2605177476828547387304605)
                      ·
                        rfl

theorem cell23_5073565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5073565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073565 prefixEnd_5073565 := by exact prefixLift 5073565
  have htrace : WordTrace (prefixWord ++ tailWord_5073565) baseStart_5073565 baseEnd_5073565 := by
    simpa [prefixWord, tailWord_5073565, baseEnd_5073565] using wordTrace_append hprefix tailTrace_5073565
  have hstable : (prefixWord ++ tailWord_5073565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073565).length < 2 ^ (prefixWord ++ tailWord_5073565).sum := by decide
  have hdescent : baseEnd_5073565 < baseStart_5073565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073572 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_5073572 : Nat := 118140960795 + 5073572 * 2 ^ 59
def prefixEnd_5073572 : Nat := 4983230072969 + 3 ^ 40 * 5073572 * 2
def baseEnd_5073572 : Nat := 2605181071193128859917073

theorem tailTrace_5073572 : CollatzResearch.WordTrace tailWord_5073572 prefixEnd_5073572 2605181071193128859917073 := by
  unfold tailWord_5073572
  simp only [CollatzResearch.WordTrace]
  refine ⟨92524186587661307978675485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123365582116881743971567313 92524186587661307978675485)
  ·
    refine ⟨34696569970372990492003307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92524186587661307978675485 34696569970372990492003307)
    ·
      refine ⟨52044854955559485738004961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34696569970372990492003307 52044854955559485738004961)
      ·
        refine ⟨39033641216669614303503721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52044854955559485738004961 39033641216669614303503721)
        ·
          refine ⟨29275230912502210727627791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39033641216669614303503721 29275230912502210727627791)
          ·
            refine ⟨43912846368753316091441687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29275230912502210727627791 43912846368753316091441687)
            ·
              refine ⟨65869269553129974137162531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43912846368753316091441687 65869269553129974137162531)
              ·
                refine ⟨98803904329694961205743797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65869269553129974137162531 98803904329694961205743797)
                ·
                  refine ⟨9262866030908902613038481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98803904329694961205743797 9262866030908902613038481)
                  ·
                    refine ⟨6947149523181676959778861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9262866030908902613038481 6947149523181676959778861)
                    ·
                      refine ⟨2605181071193128859917073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6947149523181676959778861 2605181071193128859917073)
                      ·
                        rfl

theorem cell23_5073572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_5073572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073572 prefixEnd_5073572 := by exact prefixLift 5073572
  have htrace : WordTrace (prefixWord ++ tailWord_5073572) baseStart_5073572 baseEnd_5073572 := by
    simpa [prefixWord, tailWord_5073572, baseEnd_5073572] using wordTrace_append hprefix tailTrace_5073572
  have hstable : (prefixWord ++ tailWord_5073572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073572).length < 2 ^ (prefixWord ++ tailWord_5073572).sum := by decide
  have hdescent : baseEnd_5073572 < baseStart_5073572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073589 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_5073589 : Nat := 118140960795 + 5073589 * 2 ^ 59
def prefixEnd_5073589 : Nat := 4983230072969 + 3 ^ 40 * 5073589 * 2
def baseEnd_5073589 : Nat := 2605189800364255293404495

theorem tailTrace_5073589 : CollatzResearch.WordTrace tailWord_5073589 prefixEnd_5073589 2605189800364255293404495 := by
  unfold tailWord_5073589
  simp only [CollatzResearch.WordTrace]
  refine ⟨185048993216261027860719821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123365995477507351907146547 185048993216261027860719821)
  ·
    refine ⟨69393372456097885447769933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185048993216261027860719821 69393372456097885447769933)
    ·
      refine ⟨26022514671036707042913725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69393372456097885447769933 26022514671036707042913725)
      ·
        refine ⟨9758443001638765141092647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26022514671036707042913725 9758443001638765141092647)
        ·
          refine ⟨14637664502458147711638971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9758443001638765141092647 14637664502458147711638971)
          ·
            refine ⟨21956496753687221567458457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14637664502458147711638971 21956496753687221567458457)
            ·
              refine ⟨16467372565265416175593843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21956496753687221567458457 16467372565265416175593843)
              ·
                refine ⟨24701058847898124263390765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16467372565265416175593843 24701058847898124263390765)
                ·
                  refine ⟨9262897067961796598771537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24701058847898124263390765 9262897067961796598771537)
                  ·
                    refine ⟨6947172800971347449078653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9262897067961796598771537 6947172800971347449078653)
                    ·
                      refine ⟨2605189800364255293404495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6947172800971347449078653 2605189800364255293404495)
                      ·
                        rfl

theorem cell23_5073589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_5073589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073589 prefixEnd_5073589 := by exact prefixLift 5073589
  have htrace : WordTrace (prefixWord ++ tailWord_5073589) baseStart_5073589 baseEnd_5073589 := by
    simpa [prefixWord, tailWord_5073589, baseEnd_5073589] using wordTrace_append hprefix tailTrace_5073589
  have hstable : (prefixWord ++ tailWord_5073589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073589).length < 2 ^ (prefixWord ++ tailWord_5073589).sum := by decide
  have hdescent : baseEnd_5073589 < baseStart_5073589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073590 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5073590 : Nat := 118140960795 + 5073590 * 2 ^ 59
def prefixEnd_5073590 : Nat := 4983230072969 + 3 ^ 40 * 5073590 * 2
def baseEnd_5073590 : Nat := 2605190313844909789491991

theorem tailTrace_5073590 : CollatzResearch.WordTrace tailWord_5073590 prefixEnd_5073590 2605190313844909789491991 := by
  unfold tailWord_5073590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11565564355578587814469139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123366019792838270021004149 11565564355578587814469139)
  ·
    refine ⟨17348346533367881721703709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11565564355578587814469139 17348346533367881721703709)
    ·
      refine ⟨6505629950012955645638891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17348346533367881721703709 6505629950012955645638891)
      ·
        refine ⟨9758444925019433468458337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6505629950012955645638891 9758444925019433468458337)
        ·
          refine ⟨7318833693764575101343753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9758444925019433468458337 7318833693764575101343753)
          ·
            refine ⟨5489125270323431326007815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7318833693764575101343753 5489125270323431326007815)
            ·
              refine ⟨8233687905485146989011723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489125270323431326007815 8233687905485146989011723)
              ·
                refine ⟨12350531858227720483517585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8233687905485146989011723 12350531858227720483517585)
                ·
                  refine ⟨9262898893670790362638189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12350531858227720483517585 9262898893670790362638189)
                  ·
                    refine ⟨3473587085126546385989321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9262898893670790362638189 3473587085126546385989321)
                    ·
                      refine ⟨2605190313844909789491991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473587085126546385989321 2605190313844909789491991)
                      ·
                        rfl

theorem cell23_5073590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5073590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073590 prefixEnd_5073590 := by exact prefixLift 5073590
  have htrace : WordTrace (prefixWord ++ tailWord_5073590) baseStart_5073590 baseEnd_5073590 := by
    simpa [prefixWord, tailWord_5073590, baseEnd_5073590] using wordTrace_append hprefix tailTrace_5073590
  have hstable : (prefixWord ++ tailWord_5073590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073590).length < 2 ^ (prefixWord ++ tailWord_5073590).sum := by decide
  have hdescent : baseEnd_5073590 < baseStart_5073590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073646 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_5073646 : Nat := 118140960795 + 5073646 * 2 ^ 59
def prefixEnd_5073646 : Nat := 4983230072969 + 3 ^ 40 * 5073646 * 2
def baseEnd_5073646 : Nat := 2605219068761561570391733

theorem tailTrace_5073646 : CollatzResearch.WordTrace tailWord_5073646 prefixEnd_5073646 2605219068761561570391733 := by
  unfold tailWord_5073646
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131384022131815824443099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123367381451369684397029861 23131384022131815824443099)
  ·
    refine ⟨34697076033197723736664649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23131384022131815824443099 34697076033197723736664649)
    ·
      refine ⟨26022807024898292802498487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34697076033197723736664649 26022807024898292802498487)
      ·
        refine ⟨39034210537347439203747731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26022807024898292802498487 39034210537347439203747731)
        ·
          refine ⟨58551315806021158805621597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39034210537347439203747731 58551315806021158805621597)
          ·
            refine ⟨21956743427257934552108099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58551315806021158805621597 21956743427257934552108099)
            ·
              refine ⟨32935115140886901828162149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21956743427257934552108099 32935115140886901828162149)
              ·
                refine ⟨6175334088916294092780403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32935115140886901828162149 6175334088916294092780403)
                ·
                  refine ⟨9263001133374441139170605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6175334088916294092780403 9263001133374441139170605)
                  ·
                    refine ⟨3473625425015415427188977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9263001133374441139170605 3473625425015415427188977)
                    ·
                      refine ⟨2605219068761561570391733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473625425015415427188977 2605219068761561570391733)
                      ·
                        rfl

theorem cell23_5073646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_5073646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073646 prefixEnd_5073646 := by exact prefixLift 5073646
  have htrace : WordTrace (prefixWord ++ tailWord_5073646) baseStart_5073646 baseEnd_5073646 := by
    simpa [prefixWord, tailWord_5073646, baseEnd_5073646] using wordTrace_append hprefix tailTrace_5073646
  have hstable : (prefixWord ++ tailWord_5073646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073646).length < 2 ^ (prefixWord ++ tailWord_5073646).sum := by decide
  have hdescent : baseEnd_5073646 < baseStart_5073646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073675 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9]
def baseStart_5073675 : Nat := 118140960795 + 5073675 * 2 ^ 59
def prefixEnd_5073675 : Nat := 4983230072969 + 3 ^ 40 * 5073675 * 2
def baseEnd_5073675 : Nat := 2605233959700541956929099

theorem tailTrace_5073675 : CollatzResearch.WordTrace tailWord_5073675 prefixEnd_5073675 2605233959700541956929099 := by
  unfold tailWord_5073675
  simp only [CollatzResearch.WordTrace]
  refine ⟨185052129893949464548350479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123368086595966309698900319 185052129893949464548350479)
  ·
    refine ⟨277578194840924196822525719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185052129893949464548350479 277578194840924196822525719)
    ·
      refine ⟨416367292261386295233788579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277578194840924196822525719 416367292261386295233788579)
      ·
        refine ⟨624550938392079442850682869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416367292261386295233788579 624550938392079442850682869)
        ·
          refine ⟨58551650474257447767251519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 624550938392079442850682869 58551650474257447767251519)
          ·
            refine ⟨87827475711386171650877279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58551650474257447767251519 87827475711386171650877279)
            ·
              refine ⟨131741213567079257476315919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87827475711386171650877279 131741213567079257476315919)
              ·
                refine ⟨197611820350618886214473879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131741213567079257476315919 197611820350618886214473879)
                ·
                  refine ⟨296417730525928329321710819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197611820350618886214473879 296417730525928329321710819)
                  ·
                    refine ⟨444626595788892493982566229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 296417730525928329321710819 444626595788892493982566229)
                    ·
                      refine ⟨2605233959700541956929099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 444626595788892493982566229 2605233959700541956929099)
                      ·
                        rfl

theorem cell23_5073675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_5073675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073675 prefixEnd_5073675 := by exact prefixLift 5073675
  have htrace : WordTrace (prefixWord ++ tailWord_5073675) baseStart_5073675 baseEnd_5073675 := by
    simpa [prefixWord, tailWord_5073675, baseEnd_5073675] using wordTrace_append hprefix tailTrace_5073675
  have hstable : (prefixWord ++ tailWord_5073675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073675).length < 2 ^ (prefixWord ++ tailWord_5073675).sum := by decide
  have hdescent : baseEnd_5073675 < baseStart_5073675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073676 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 2, 2, 2]
def baseStart_5073676 : Nat := 118140960795 + 5073676 * 2 ^ 59
def prefixEnd_5073676 : Nat := 4983230072969 + 3 ^ 40 * 5073676 * 2
def baseEnd_5073676 : Nat := 2605234473181196453016595

theorem tailTrace_5073676 : CollatzResearch.WordTrace tailWord_5073676 prefixEnd_5073676 2605234473181196453016595 := by
  unfold tailWord_5073676
  simp only [CollatzResearch.WordTrace]
  refine ⟨92526083183472920859568441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123368110911297227812757921 92526083183472920859568441)
  ·
    refine ⟨69394562387604690644676331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92526083183472920859568441 69394562387604690644676331)
    ·
      refine ⟨104091843581407035967014497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69394562387604690644676331 104091843581407035967014497)
      ·
        refine ⟨78068882686055276975260873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104091843581407035967014497 78068882686055276975260873)
        ·
          refine ⟨58551662014541457731445655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78068882686055276975260873 58551662014541457731445655)
          ·
            refine ⟨87827493021812186597168483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58551662014541457731445655 87827493021812186597168483)
            ·
              refine ⟨131741239532718279895752725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87827493021812186597168483 131741239532718279895752725)
              ·
                refine ⟨6175370603096169370113409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131741239532718279895752725 6175370603096169370113409)
                ·
                  refine ⟨4631527952322127027585057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6175370603096169370113409 4631527952322127027585057)
                  ·
                    refine ⟨3473645964241595270688793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631527952322127027585057 3473645964241595270688793)
                    ·
                      refine ⟨2605234473181196453016595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473645964241595270688793 2605234473181196453016595)
                      ·
                        rfl

theorem cell23_5073676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_5073676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073676 prefixEnd_5073676 := by exact prefixLift 5073676
  have htrace : WordTrace (prefixWord ++ tailWord_5073676) baseStart_5073676 baseEnd_5073676 := by
    simpa [prefixWord, tailWord_5073676, baseEnd_5073676] using wordTrace_append hprefix tailTrace_5073676
  have hstable : (prefixWord ++ tailWord_5073676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073676).length < 2 ^ (prefixWord ++ tailWord_5073676).sum := by decide
  have hdescent : baseEnd_5073676 < baseStart_5073676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073759 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 3, 4]
def baseStart_5073759 : Nat := 118140960795 + 5073759 * 2 ^ 59
def prefixEnd_5073759 : Nat := 4983230072969 + 3 ^ 40 * 5073759 * 2
def baseEnd_5073759 : Nat := 868425697358506542759571

theorem tailTrace_5073759 : CollatzResearch.WordTrace tailWord_5073759 prefixEnd_5073759 868425697358506542759571 := by
  unfold tailWord_5073759
  simp only [CollatzResearch.WordTrace]
  refine ⟨185055193625645146894408331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123370129083763431262938887 185055193625645146894408331)
  ·
    refine ⟨277582790438467720341612497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185055193625645146894408331 277582790438467720341612497)
    ·
      refine ⟨208187092828850790256209373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277582790438467720341612497 208187092828850790256209373)
      ·
        refine ⟨78070159810819046346078515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208187092828850790256209373 78070159810819046346078515)
        ·
          refine ⟨117105239716228569519117773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78070159810819046346078515 117105239716228569519117773)
          ·
            refine ⟨43914464893585713569669165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117105239716228569519117773 43914464893585713569669165)
            ·
              refine ⟨16467924335094642588625937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43914464893585713569669165 16467924335094642588625937)
              ·
                refine ⟨12350943251320981941469453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16467924335094642588625937 12350943251320981941469453)
                ·
                  refine ⟨4631603719245368228051045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12350943251320981941469453 4631603719245368228051045)
                  ·
                    refine ⟨868425697358506542759571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631603719245368228051045 868425697358506542759571)
                    ·
                      rfl

theorem cell23_5073759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_5073759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073759 prefixEnd_5073759 := by exact prefixLift 5073759
  have htrace : WordTrace (prefixWord ++ tailWord_5073759) baseStart_5073759 baseEnd_5073759 := by
    simpa [prefixWord, tailWord_5073759, baseEnd_5073759] using wordTrace_append hprefix tailTrace_5073759
  have hstable : (prefixWord ++ tailWord_5073759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073759).length < 2 ^ (prefixWord ++ tailWord_5073759).sum := by decide
  have hdescent : baseEnd_5073759 < baseStart_5073759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073772 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 8]
def baseStart_5073772 : Nat := 118140960795 + 5073772 * 2 ^ 59
def prefixEnd_5073772 : Nat := 4983230072969 + 3 ^ 40 * 5073772 * 2
def baseEnd_5073772 : Nat := 289475974147114230824017

theorem tailTrace_5073772 : CollatzResearch.WordTrace tailWord_5073772 prefixEnd_5073772 289475974147114230824017 := by
  unfold tailWord_5073772
  simp only [CollatzResearch.WordTrace]
  refine ⟨92527833887299025057315785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123370445183065366743087713 92527833887299025057315785)
  ·
    refine ⟨69395875415474268792986839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92527833887299025057315785 69395875415474268792986839)
    ·
      refine ⟨104093813123211403189480259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69395875415474268792986839 104093813123211403189480259)
      ·
        refine ⟨156140719684817104784220389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104093813123211403189480259 156140719684817104784220389)
        ·
          refine ⟨29276384940903207147041323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156140719684817104784220389 29276384940903207147041323)
          ·
            refine ⟨43914577411354810720561985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29276384940903207147041323 43914577411354810720561985)
            ·
              refine ⟨32935933058516108040421489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43914577411354810720561985 32935933058516108040421489)
              ·
                refine ⟨24701949793887081030316117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32935933058516108040421489 24701949793887081030316117)
                ·
                  refine ⟨289475974147114230824017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24701949793887081030316117 289475974147114230824017)
                  ·
                    rfl

theorem cell23_5073772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_5073772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073772 prefixEnd_5073772 := by exact prefixLift 5073772
  have htrace : WordTrace (prefixWord ++ tailWord_5073772) baseStart_5073772 baseEnd_5073772 := by
    simpa [prefixWord, tailWord_5073772, baseEnd_5073772] using wordTrace_append hprefix tailTrace_5073772
  have hstable : (prefixWord ++ tailWord_5073772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073772).length < 2 ^ (prefixWord ++ tailWord_5073772).sum := by decide
  have hdescent : baseEnd_5073772 < baseStart_5073772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073776 : List Nat := [2, 1, 1, 1, 4, 1, 3, 5, 1, 4]
def baseStart_5073776 : Nat := 118140960795 + 5073776 * 2 ^ 59
def prefixEnd_5073776 : Nat := 4983230072969 + 3 ^ 40 * 5073776 * 2
def baseEnd_5073776 : Nat := 868428607082215353922045

theorem tailTrace_5073776 : CollatzResearch.WordTrace tailWord_5073776 prefixEnd_5073776 868428607082215353922045 := by
  unfold tailWord_5073776
  simp only [CollatzResearch.WordTrace]
  refine ⟨92527906833291779398888591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123370542444389039198518121 92527906833291779398888591)
  ·
    refine ⟨138791860249937669098332887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92527906833291779398888591 138791860249937669098332887)
    ·
      refine ⟨208187790374906503647499331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138791860249937669098332887 208187790374906503647499331)
      ·
        refine ⟨312281685562359755471248997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208187790374906503647499331 312281685562359755471248997)
        ·
          refine ⟨58552816042942454150859187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312281685562359755471248997 58552816042942454150859187)
          ·
            refine ⟨87829224064413681226288781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58552816042942454150859187 87829224064413681226288781)
            ·
              refine ⟨32935959024155130459858293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87829224064413681226288781 32935959024155130459858293)
              ·
                refine ⟨3087746158514543480611715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32935959024155130459858293 3087746158514543480611715)
                ·
                  refine ⟨4631619237771815220917573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087746158514543480611715 4631619237771815220917573)
                  ·
                    refine ⟨868428607082215353922045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631619237771815220917573 868428607082215353922045)
                    ·
                      rfl

theorem cell23_5073776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 4].length) (baseStart_5073776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073776 prefixEnd_5073776 := by exact prefixLift 5073776
  have htrace : WordTrace (prefixWord ++ tailWord_5073776) baseStart_5073776 baseEnd_5073776 := by
    simpa [prefixWord, tailWord_5073776, baseEnd_5073776] using wordTrace_append hprefix tailTrace_5073776
  have hstable : (prefixWord ++ tailWord_5073776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073776).length < 2 ^ (prefixWord ++ tailWord_5073776).sum := by decide
  have hdescent : baseEnd_5073776 < baseStart_5073776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073789 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 6]
def baseStart_5073789 : Nat := 118140960795 + 5073789 * 2 ^ 59
def prefixEnd_5073789 : Nat := 4983230072969 + 3 ^ 40 * 5073789 * 2
def baseEnd_5073789 : Nat := 289476944055017167878175

theorem tailTrace_5073789 : CollatzResearch.WordTrace tailWord_5073789 prefixEnd_5073789 289476944055017167878175 := by
  unfold tailWord_5073789
  simp only [CollatzResearch.WordTrace]
  refine ⟨185056287815536462018000421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123370858543690974678666947 185056287815536462018000421)
  ·
    refine ⟨34698053965413086628375079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185056287815536462018000421 34698053965413086628375079)
    ·
      refine ⟨52047080948119629942562619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34698053965413086628375079 52047080948119629942562619)
      ·
        refine ⟨78070621422179444913843929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52047080948119629942562619 78070621422179444913843929)
        ·
          refine ⟨58552966066634583685382947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78070621422179444913843929 58552966066634583685382947)
          ·
            refine ⟨87829449099951875528074421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58552966066634583685382947 87829449099951875528074421)
            ·
              refine ⟨8234010853120488330756977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87829449099951875528074421 8234010853120488330756977)
              ·
                refine ⟨6175508139840366248067733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8234010853120488330756977 6175508139840366248067733)
                ·
                  refine ⟨289476944055017167878175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6175508139840366248067733 289476944055017167878175)
                  ·
                    rfl

theorem cell23_5073789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_5073789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073789 prefixEnd_5073789 := by exact prefixLift 5073789
  have htrace : WordTrace (prefixWord ++ tailWord_5073789) baseStart_5073789 baseEnd_5073789 := by
    simpa [prefixWord, tailWord_5073789, baseEnd_5073789] using wordTrace_append hprefix tailTrace_5073789
  have hstable : (prefixWord ++ tailWord_5073789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073789).length < 2 ^ (prefixWord ++ tailWord_5073789).sum := by decide
  have hdescent : baseEnd_5073789 < baseStart_5073789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073850 : List Nat := [3, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3]
def baseStart_5073850 : Nat := 118140960795 + 5073850 * 2 ^ 59
def prefixEnd_5073850 : Nat := 4983230072969 + 3 ^ 40 * 5073850 * 2
def baseEnd_5073850 : Nat := 2605323818815078772240795

theorem tailTrace_5073850 : CollatzResearch.WordTrace tailWord_5073850 prefixEnd_5073850 2605323818815078772240795 := by
  unfold tailWord_5073850
  simp only [CollatzResearch.WordTrace]
  refine ⟨46264628167078867358992751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123372341778876979623980669 46264628167078867358992751)
  ·
    refine ⟨69396942250618301038489127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46264628167078867358992751 69396942250618301038489127)
    ·
      refine ⟨104095413375927451557733691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69396942250618301038489127 104095413375927451557733691)
      ·
        refine ⟨156143120063891177336600537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104095413375927451557733691 156143120063891177336600537)
        ·
          refine ⟨117107340047918383002450403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156143120063891177336600537 117107340047918383002450403)
          ·
            refine ⟨175661010071877574503675605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117107340047918383002450403 175661010071877574503675605)
            ·
              refine ⟨4117054923559630652429897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 175661010071877574503675605 4117054923559630652429897)
              ·
                refine ⟨3087791192669722989322423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4117054923559630652429897 3087791192669722989322423)
                ·
                  refine ⟨4631686789004584483983635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087791192669722989322423 4631686789004584483983635)
                  ·
                    refine ⟨6947530183506876725975453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4631686789004584483983635 6947530183506876725975453)
                    ·
                      refine ⟨2605323818815078772240795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6947530183506876725975453 2605323818815078772240795)
                      ·
                        rfl

theorem cell23_5073850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_5073850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073850 prefixEnd_5073850 := by exact prefixLift 5073850
  have htrace : WordTrace (prefixWord ++ tailWord_5073850) baseStart_5073850 baseEnd_5073850 := by
    simpa [prefixWord, tailWord_5073850, baseEnd_5073850] using wordTrace_append hprefix tailTrace_5073850
  have hstable : (prefixWord ++ tailWord_5073850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073850).length < 2 ^ (prefixWord ++ tailWord_5073850).sum := by decide
  have hdescent : baseEnd_5073850 < baseStart_5073850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073859 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 3]
def baseStart_5073859 : Nat := 118140960795 + 5073859 * 2 ^ 59
def prefixEnd_5073859 : Nat := 4983230072969 + 3 ^ 40 * 5073859 * 2
def baseEnd_5073859 : Nat := 2605328440140969237028253

theorem tailTrace_5073859 : CollatzResearch.WordTrace tailWord_5073859 prefixEnd_5073859 2605328440140969237028253 := by
  unfold tailWord_5073859
  simp only [CollatzResearch.WordTrace]
  refine ⟨185058840925282863973048631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123372560616855242648699087 185058840925282863973048631)
  ·
    refine ⟨277588261387924295959572947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185058840925282863973048631 277588261387924295959572947)
    ·
      refine ⟨416382392081886443939359421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277588261387924295959572947 416382392081886443939359421)
      ·
        refine ⟨156143397030707416477259783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416382392081886443939359421 156143397030707416477259783)
        ·
          refine ⟨234215095546061124715889675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156143397030707416477259783 234215095546061124715889675)
          ·
            refine ⟨351322643319091687073834513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234215095546061124715889675 351322643319091687073834513)
            ·
              refine ⟨263491982489318765305375885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351322643319091687073834513 263491982489318765305375885)
              ·
                refine ⟨98809493433494536989515957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263491982489318765305375885 98809493433494536989515957)
                ·
                  refine ⟨9263390009390112842767121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98809493433494536989515957 9263390009390112842767121)
                  ·
                    refine ⟨6947542507042584632075341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9263390009390112842767121 6947542507042584632075341)
                    ·
                      refine ⟨2605328440140969237028253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6947542507042584632075341 2605328440140969237028253)
                      ·
                        rfl

theorem cell23_5073859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_5073859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073859 prefixEnd_5073859 := by exact prefixLift 5073859
  have htrace : WordTrace (prefixWord ++ tailWord_5073859) baseStart_5073859 baseEnd_5073859 := by
    simpa [prefixWord, tailWord_5073859, baseEnd_5073859] using wordTrace_append hprefix tailTrace_5073859
  have hstable : (prefixWord ++ tailWord_5073859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073859).length < 2 ^ (prefixWord ++ tailWord_5073859).sum := by decide
  have hdescent : baseEnd_5073859 < baseStart_5073859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073956 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_5073956 : Nat := 118140960795 + 5073956 * 2 ^ 59
def prefixEnd_5073956 : Nat := 4983230072969 + 3 ^ 40 * 5073956 * 2
def baseEnd_5073956 : Nat := 868459415921485119171769

theorem tailTrace_5073956 : CollatzResearch.WordTrace tailWord_5073956 prefixEnd_5073956 868459415921485119171769 := by
  unfold tailWord_5073956
  simp only [CollatzResearch.WordTrace]
  refine ⟨92531189402965724769664861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123374919203954299692886481 92531189402965724769664861)
  ·
    refine ⟨34699196026112146788624323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92531189402965724769664861 34699196026112146788624323)
    ·
      refine ⟨52048794039168220182936485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34699196026112146788624323 52048794039168220182936485)
      ·
        refine ⟨9759148882344041284300591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52048794039168220182936485 9759148882344041284300591)
        ·
          refine ⟨14638723323516061926450887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9759148882344041284300591 14638723323516061926450887)
          ·
            refine ⟨21958084985274092889676331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14638723323516061926450887 21958084985274092889676331)
            ·
              refine ⟨32937127477911139334514497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21958084985274092889676331 32937127477911139334514497)
              ·
                refine ⟨24702845608433354500885873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32937127477911139334514497 24702845608433354500885873)
                ·
                  refine ⟨18527134206325015875664405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24702845608433354500885873 18527134206325015875664405)
                  ·
                    refine ⟨868459415921485119171769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18527134206325015875664405 868459415921485119171769)
                    ·
                      rfl

theorem cell23_5073956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_5073956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073956 prefixEnd_5073956 := by exact prefixLift 5073956
  have htrace : WordTrace (prefixWord ++ tailWord_5073956) baseStart_5073956 baseEnd_5073956 := by
    simpa [prefixWord, tailWord_5073956, baseEnd_5073956] using wordTrace_append hprefix tailTrace_5073956
  have hstable : (prefixWord ++ tailWord_5073956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073956).length < 2 ^ (prefixWord ++ tailWord_5073956).sum := by decide
  have hdescent : baseEnd_5073956 < baseStart_5073956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073963 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 4, 2, 2]
def baseStart_5073963 : Nat := 118140960795 + 5073963 * 2 ^ 59
def prefixEnd_5073963 : Nat := 4983230072969 + 3 ^ 40 * 5073963 * 2
def baseEnd_5073963 : Nat := 2605381842129036830127775

theorem tailTrace_5073963 : CollatzResearch.WordTrace tailWord_5073963 prefixEnd_5073963 2605381842129036830127775 := by
  unfold tailWord_5073963
  simp only [CollatzResearch.WordTrace]
  refine ⟨185062634116906089734834543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123375089411270726489889695 185062634116906089734834543)
  ·
    refine ⟨277593951175359134602251815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185062634116906089734834543 277593951175359134602251815)
    ·
      refine ⟨416390926763038701903377723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277593951175359134602251815 416390926763038701903377723)
      ·
        refine ⟨624586390144558052855066585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416390926763038701903377723 624586390144558052855066585)
        ·
          refine ⟨468439792608418539641299939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624586390144558052855066585 468439792608418539641299939)
          ·
            refine ⟨702659688912627809461949909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468439792608418539641299939 702659688912627809461949909)
            ·
              refine ⟨16468586458889714284264451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 702659688912627809461949909 16468586458889714284264451)
              ·
                refine ⟨24702879688334571426396677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16468586458889714284264451 24702879688334571426396677)
                ·
                  refine ⟨4631789941562732142449377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24702879688334571426396677 4631789941562732142449377)
                  ·
                    refine ⟨3473842456172049106837033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631789941562732142449377 3473842456172049106837033)
                    ·
                      refine ⟨2605381842129036830127775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473842456172049106837033 2605381842129036830127775)
                      ·
                        rfl

theorem cell23_5073963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 2, 2].length) (baseStart_5073963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073963 prefixEnd_5073963 := by exact prefixLift 5073963
  have htrace : WordTrace (prefixWord ++ tailWord_5073963) baseStart_5073963 baseEnd_5073963 := by
    simpa [prefixWord, tailWord_5073963, baseEnd_5073963] using wordTrace_append hprefix tailTrace_5073963
  have hstable : (prefixWord ++ tailWord_5073963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073963).length < 2 ^ (prefixWord ++ tailWord_5073963).sum := by decide
  have hdescent : baseEnd_5073963 < baseStart_5073963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073976 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_5073976 : Nat := 118140960795 + 5073976 * 2 ^ 59
def prefixEnd_5073976 : Nat := 4983230072969 + 3 ^ 40 * 5073976 * 2
def baseEnd_5073976 : Nat := 2605388517377545279265215

theorem tailTrace_5073976 : CollatzResearch.WordTrace tailWord_5073976 prefixEnd_5073976 2605388517377545279265215 := by
  unfold tailWord_5073976
  simp only [CollatzResearch.WordTrace]
  refine ⟨92531554132929496477528891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123375405510572661970038521 92531554132929496477528891)
  ·
    refine ⟨138797331199394244716293337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92531554132929496477528891 138797331199394244716293337)
    ·
      refine ⟨104097998399545683537220003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138797331199394244716293337 104097998399545683537220003)
      ·
        refine ⟨156146997599318525305830005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104097998399545683537220003 156146997599318525305830005)
        ·
          refine ⟨14638781024936111747421563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156146997599318525305830005 14638781024936111747421563)
          ·
            refine ⟨21958171537404167621132345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14638781024936111747421563 21958171537404167621132345)
            ·
              refine ⟨16468628653053125715849259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21958171537404167621132345 16468628653053125715849259)
              ·
                refine ⟨24702942979579688573773889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16468628653053125715849259 24702942979579688573773889)
                ·
                  refine ⟨18527207234684766430330417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24702942979579688573773889 18527207234684766430330417)
                  ·
                    refine ⟨13895405426013574822747813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18527207234684766430330417 13895405426013574822747813)
                    ·
                      refine ⟨2605388517377545279265215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13895405426013574822747813 2605388517377545279265215)
                      ·
                        rfl

theorem cell23_5073976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_5073976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073976 prefixEnd_5073976 := by exact prefixLift 5073976
  have htrace : WordTrace (prefixWord ++ tailWord_5073976) baseStart_5073976 baseEnd_5073976 := by
    simpa [prefixWord, tailWord_5073976, baseEnd_5073976] using wordTrace_append hprefix tailTrace_5073976
  have hstable : (prefixWord ++ tailWord_5073976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073976).length < 2 ^ (prefixWord ++ tailWord_5073976).sum := by decide
  have hdescent : baseEnd_5073976 < baseStart_5073976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5073980 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_5073980 : Nat := 118140960795 + 5073980 * 2 ^ 59
def prefixEnd_5073980 : Nat := 4983230072969 + 3 ^ 40 * 5073980 * 2
def baseEnd_5073980 : Nat := 2605390571300163263615197

theorem tailTrace_5073980 : CollatzResearch.WordTrace tailWord_5073980 prefixEnd_5073980 2605390571300163263615197 := by
  unfold tailWord_5073980
  simp only [CollatzResearch.WordTrace]
  refine ⟨92531627078922250819101697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123375502771896334425468929 92531627078922250819101697)
  ·
    refine ⟨69398720309191688114326273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92531627078922250819101697 69398720309191688114326273)
    ·
      refine ⟨52049040231893766085744705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69398720309191688114326273 52049040231893766085744705)
      ·
        refine ⟨39036780173920324564308529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52049040231893766085744705 39036780173920324564308529)
        ·
          refine ⟨29277585130440243423231397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39036780173920324564308529 29277585130440243423231397)
          ·
            refine ⟨5489547211957545641855887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29277585130440243423231397 5489547211957545641855887)
            ·
              refine ⟨8234320817936318462783831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489547211957545641855887 8234320817936318462783831)
              ·
                refine ⟨12351481226904477694175747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8234320817936318462783831 12351481226904477694175747)
                ·
                  refine ⟨18527221840356716541263621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12351481226904477694175747 18527221840356716541263621)
                  ·
                    refine ⟨3473854095066884351486929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18527221840356716541263621 3473854095066884351486929)
                    ·
                      refine ⟨2605390571300163263615197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473854095066884351486929 2605390571300163263615197)
                      ·
                        rfl

theorem cell23_5073980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_5073980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5073980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5073980 prefixEnd_5073980 := by exact prefixLift 5073980
  have htrace : WordTrace (prefixWord ++ tailWord_5073980) baseStart_5073980 baseEnd_5073980 := by
    simpa [prefixWord, tailWord_5073980, baseEnd_5073980] using wordTrace_append hprefix tailTrace_5073980
  have hstable : (prefixWord ++ tailWord_5073980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5073980).length < 2 ^ (prefixWord ++ tailWord_5073980).sum := by decide
  have hdescent : baseEnd_5073980 < baseStart_5073980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5073980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074014 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5074014 : Nat := 118140960795 + 5074014 * 2 ^ 59
def prefixEnd_5074014 : Nat := 4983230072969 + 3 ^ 40 * 5074014 * 2
def baseEnd_5074014 : Nat := 2605408029642416130590041

theorem tailTrace_5074014 : CollatzResearch.WordTrace tailWord_5074014 prefixEnd_5074014 2605408029642416130590041 := by
  unfold tailWord_5074014
  simp only [CollatzResearch.WordTrace]
  refine ⟨23133061779965165680617637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123376329493147550296627397 23133061779965165680617637)
  ·
    refine ⟨4337449083743468565115807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23133061779965165680617637 4337449083743468565115807)
    ·
      refine ⟨6506173625615202847673711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337449083743468565115807 6506173625615202847673711)
      ·
        refine ⟨9759260438422804271510567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506173625615202847673711 9759260438422804271510567)
        ·
          refine ⟨14638890657634206407265851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9759260438422804271510567 14638890657634206407265851)
          ·
            refine ⟨21958335986451309610898777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14638890657634206407265851 21958335986451309610898777)
            ·
              refine ⟨16468751989838482208174083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21958335986451309610898777 16468751989838482208174083)
              ·
                refine ⟨24703127984757723312261125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16468751989838482208174083 24703127984757723312261125)
                ·
                  refine ⟨4631836497142073121048961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24703127984757723312261125 4631836497142073121048961)
                  ·
                    refine ⟨3473877372856554840786721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631836497142073121048961 3473877372856554840786721)
                    ·
                      refine ⟨2605408029642416130590041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473877372856554840786721 2605408029642416130590041)
                      ·
                        rfl

theorem cell23_5074014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5074014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074014 prefixEnd_5074014 := by exact prefixLift 5074014
  have htrace : WordTrace (prefixWord ++ tailWord_5074014) baseStart_5074014 baseEnd_5074014 := by
    simpa [prefixWord, tailWord_5074014, baseEnd_5074014] using wordTrace_append hprefix tailTrace_5074014
  have hstable : (prefixWord ++ tailWord_5074014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074014).length < 2 ^ (prefixWord ++ tailWord_5074014).sum := by decide
  have hdescent : baseEnd_5074014 < baseStart_5074014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074016 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 2, 5]
def baseStart_5074016 : Nat := 118140960795 + 5074016 * 2 ^ 59
def prefixEnd_5074016 : Nat := 4983230072969 + 3 ^ 40 * 5074016 * 2
def baseEnd_5074016 : Nat := 868469685534575040921677

theorem tailTrace_5074016 : CollatzResearch.WordTrace tailWord_5074016 prefixEnd_5074016 868469685534575040921677 := by
  unfold tailWord_5074016
  simp only [CollatzResearch.WordTrace]
  refine ⟨92532283592857039893256951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123376378123809386524342601 92532283592857039893256951)
  ·
    refine ⟨138798425389285559839885427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92532283592857039893256951 138798425389285559839885427)
    ·
      refine ⟨208197638083928339759828141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138798425389285559839885427 208197638083928339759828141)
      ·
        refine ⟨78074114281473127409935553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208197638083928339759828141 78074114281473127409935553)
        ·
          refine ⟨58555585711104845557451665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78074114281473127409935553 58555585711104845557451665)
          ·
            refine ⟨43916689283328634168088749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58555585711104845557451665 43916689283328634168088749)
            ·
              refine ⟨16468758481248237813033281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43916689283328634168088749 16468758481248237813033281)
              ·
                refine ⟨12351568860936178359774961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16468758481248237813033281 12351568860936178359774961)
                ·
                  refine ⟨9263676645702133769831221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12351568860936178359774961 9263676645702133769831221)
                  ·
                    refine ⟨868469685534575040921677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9263676645702133769831221 868469685534575040921677)
                    ·
                      rfl

theorem cell23_5074016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_5074016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074016 prefixEnd_5074016 := by exact prefixLift 5074016
  have htrace : WordTrace (prefixWord ++ tailWord_5074016) baseStart_5074016 baseEnd_5074016 := by
    simpa [prefixWord, tailWord_5074016, baseEnd_5074016] using wordTrace_append hprefix tailTrace_5074016
  have hstable : (prefixWord ++ tailWord_5074016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074016).length < 2 ^ (prefixWord ++ tailWord_5074016).sum := by decide
  have hdescent : baseEnd_5074016 < baseStart_5074016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074026 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5074026 : Nat := 118140960795 + 5074026 * 2 ^ 59
def prefixEnd_5074026 : Nat := 4983230072969 + 3 ^ 40 * 5074026 * 2
def baseEnd_5074026 : Nat := 2605414191410270083639985

theorem tailTrace_5074026 : CollatzResearch.WordTrace tailWord_5074026 prefixEnd_5074026 2605414191410270083639985 := by
  unfold tailWord_5074026
  simp only [CollatzResearch.WordTrace]
  refine ⟨46266232978919462873594483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123376621277118567662918621 46266232978919462873594483)
  ·
    refine ⟨69399349468379194310391725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46266232978919462873594483 69399349468379194310391725)
    ·
      refine ⟨26024756050642197866396897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69399349468379194310391725 26024756050642197866396897)
      ·
        refine ⟨19518567037981648399797673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26024756050642197866396897 19518567037981648399797673)
        ·
          refine ⟨14638925278486236299848255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19518567037981648399797673 14638925278486236299848255)
          ·
            refine ⟨21958387917729354449772383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14638925278486236299848255 21958387917729354449772383)
            ·
              refine ⟨32937581876594031674658575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21958387917729354449772383 32937581876594031674658575)
              ·
                refine ⟨49406372814891047511987863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32937581876594031674658575 49406372814891047511987863)
                ·
                  refine ⟨74109559222336571267981795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49406372814891047511987863 74109559222336571267981795)
                  ·
                    refine ⟨111164338833504856901972693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74109559222336571267981795 111164338833504856901972693)
                    ·
                      refine ⟨2605414191410270083639985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111164338833504856901972693 2605414191410270083639985)
                      ·
                        rfl

theorem cell23_5074026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5074026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074026 prefixEnd_5074026 := by exact prefixLift 5074026
  have htrace : WordTrace (prefixWord ++ tailWord_5074026) baseStart_5074026 baseEnd_5074026 := by
    simpa [prefixWord, tailWord_5074026, baseEnd_5074026] using wordTrace_append hprefix tailTrace_5074026
  have hstable : (prefixWord ++ tailWord_5074026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074026).length < 2 ^ (prefixWord ++ tailWord_5074026).sum := by decide
  have hdescent : baseEnd_5074026 < baseStart_5074026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074059 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 10]
def baseStart_5074059 : Nat := 118140960795 + 5074059 * 2 ^ 59
def prefixEnd_5074059 : Nat := 4983230072969 + 3 ^ 40 * 5074059 * 2
def baseEnd_5074059 : Nat := 289492348474652050503037

theorem tailTrace_5074059 : CollatzResearch.WordTrace tailWord_5074059 prefixEnd_5074059 289492348474652050503037 := by
  unfold tailWord_5074059
  simp only [CollatzResearch.WordTrace]
  refine ⟨185066135524558298130329231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123377423683038865420219487 185066135524558298130329231)
  ·
    refine ⟨277599203286837447195493847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185066135524558298130329231 277599203286837447195493847)
    ·
      refine ⟨416398804930256170793240771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277599203286837447195493847 416398804930256170793240771)
      ·
        refine ⟨624598207395384256189861157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416398804930256170793240771 624598207395384256189861157)
        ·
          refine ⟨117112163886634548035598967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 624598207395384256189861157 117112163886634548035598967)
          ·
            refine ⟨175668245829951822053398451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117112163886634548035598967 175668245829951822053398451)
            ·
              refine ⟨263502368744927733080097677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175668245829951822053398451 263502368744927733080097677)
              ·
                refine ⟨98813388279347899905036629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263502368744927733080097677 98813388279347899905036629)
                ·
                  refine ⟨289492348474652050503037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 98813388279347899905036629 289492348474652050503037)
                  ·
                    rfl

theorem cell23_5074059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 10].length) (baseStart_5074059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074059 prefixEnd_5074059 := by exact prefixLift 5074059
  have htrace : WordTrace (prefixWord ++ tailWord_5074059) baseStart_5074059 baseEnd_5074059 := by
    simpa [prefixWord, tailWord_5074059, baseEnd_5074059] using wordTrace_append hprefix tailTrace_5074059
  have hstable : (prefixWord ++ tailWord_5074059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074059).length < 2 ^ (prefixWord ++ tailWord_5074059).sum := by decide
  have hdescent : baseEnd_5074059 < baseStart_5074059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074080 : List Nat := [2, 1, 1, 4, 2, 1, 3, 4, 1, 4]
def baseStart_5074080 : Nat := 118140960795 + 5074080 * 2 ^ 59
def prefixEnd_5074080 : Nat := 4983230072969 + 3 ^ 40 * 5074080 * 2
def baseEnd_5074080 : Nat := 868480639788537624121579

theorem tailTrace_5074080 : CollatzResearch.WordTrace tailWord_5074080 prefixEnd_5074080 868480639788537624121579 := by
  unfold tailWord_5074080
  simp only [CollatzResearch.WordTrace]
  refine ⟨92533450728741109358421847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123377934304988145811229129 92533450728741109358421847)
  ·
    refine ⟨138800176093111664037632771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92533450728741109358421847 138800176093111664037632771)
    ·
      refine ⟨208200264139667496056449157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138800176093111664037632771 208200264139667496056449157)
      ·
        refine ⟨39037549526187655510584217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208200264139667496056449157 39037549526187655510584217)
        ·
          refine ⟨29278162144640741632938163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39037549526187655510584217 29278162144640741632938163)
          ·
            refine ⟨43917243216961112449407245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29278162144640741632938163 43917243216961112449407245)
            ·
              refine ⟨16468966206360417168527717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43917243216961112449407245 16468966206360417168527717)
              ·
                refine ⟨3087931163692578219098947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16468966206360417168527717 3087931163692578219098947)
                ·
                  refine ⟨4631896745538867328648421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087931163692578219098947 4631896745538867328648421)
                  ·
                    refine ⟨868480639788537624121579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4631896745538867328648421 868480639788537624121579)
                    ·
                      rfl

theorem cell23_5074080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 4].length) (baseStart_5074080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074080 prefixEnd_5074080 := by exact prefixLift 5074080
  have htrace : WordTrace (prefixWord ++ tailWord_5074080) baseStart_5074080 baseEnd_5074080 := by
    simpa [prefixWord, tailWord_5074080, baseEnd_5074080] using wordTrace_append hprefix tailTrace_5074080
  have hstable : (prefixWord ++ tailWord_5074080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074080).length < 2 ^ (prefixWord ++ tailWord_5074080).sum := by decide
  have hdescent : baseEnd_5074080 < baseStart_5074080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074130 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_5074130 : Nat := 118140960795 + 5074130 * 2 ^ 59
def prefixEnd_5074130 : Nat := 4983230072969 + 3 ^ 40 * 5074130 * 2
def baseEnd_5074130 : Nat := 2605467593398337676739507

theorem tailTrace_5074130 : CollatzResearch.WordTrace tailWord_5074130 prefixEnd_5074130 2605467593398337676739507 := by
  unfold tailWord_5074130
  simp only [CollatzResearch.WordTrace]
  refine ⟨46267181276825269314040961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123379150071534051504109229 46267181276825269314040961)
  ·
    refine ⟨34700385957618951985530721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46267181276825269314040961 34700385957618951985530721)
    ·
      refine ⟨26025289468214213989148041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34700385957618951985530721 26025289468214213989148041)
      ·
        refine ⟨19518967101160660491861031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26025289468214213989148041 19518967101160660491861031)
        ·
          refine ⟨29278450651740990737791547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19518967101160660491861031 29278450651740990737791547)
          ·
            refine ⟨43917675977611486106687321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29278450651740990737791547 43917675977611486106687321)
            ·
              refine ⟨32938256983208614580015491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43917675977611486106687321 32938256983208614580015491)
              ·
                refine ⟨49407385474812921870023237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32938256983208614580015491 49407385474812921870023237)
                ·
                  refine ⟨9263884776527422850629357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49407385474812921870023237 9263884776527422850629357)
                  ·
                    refine ⟨3473956791197783568986009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9263884776527422850629357 3473956791197783568986009)
                    ·
                      refine ⟨2605467593398337676739507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3473956791197783568986009 2605467593398337676739507)
                      ·
                        rfl

theorem cell23_5074130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_5074130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074130 prefixEnd_5074130 := by exact prefixLift 5074130
  have htrace : WordTrace (prefixWord ++ tailWord_5074130) baseStart_5074130 baseEnd_5074130 := by
    simpa [prefixWord, tailWord_5074130, baseEnd_5074130] using wordTrace_append hprefix tailTrace_5074130
  have hstable : (prefixWord ++ tailWord_5074130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074130).length < 2 ^ (prefixWord ++ tailWord_5074130).sum := by decide
  have hdescent : baseEnd_5074130 < baseStart_5074130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074180 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_5074180 : Nat := 118140960795 + 5074180 * 2 ^ 59
def prefixEnd_5074180 : Nat := 4983230072969 + 3 ^ 40 * 5074180 * 2
def baseEnd_5074180 : Nat := 2605493267431062481114277

theorem tailTrace_5074180 : CollatzResearch.WordTrace tailWord_5074180 prefixEnd_5074180 2605493267431062481114277 := by
  unfold tailWord_5074180
  simp only [CollatzResearch.WordTrace]
  refine ⟨92535274378559967897741997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123380365838079957196989329 92535274378559967897741997)
  ·
    refine ⟨34700727891959987961653249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92535274378559967897741997 34700727891959987961653249)
    ·
      refine ⟨26025545918969990971239937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34700727891959987961653249 26025545918969990971239937)
      ·
        refine ⟨19519159439227493228429953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26025545918969990971239937 19519159439227493228429953)
        ·
          refine ⟨14639369579420619921322465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19519159439227493228429953 14639369579420619921322465)
          ·
            refine ⟨10979527184565464940991849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14639369579420619921322465 10979527184565464940991849)
            ·
              refine ⟨8234645388424098705743887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10979527184565464940991849 8234645388424098705743887)
              ·
                refine ⟨12351968082636148058615831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8234645388424098705743887 12351968082636148058615831)
                ·
                  refine ⟨18527952123954222087923747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12351968082636148058615831 18527952123954222087923747)
                  ·
                    refine ⟨27791928185931333131885621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18527952123954222087923747 27791928185931333131885621)
                    ·
                      refine ⟨2605493267431062481114277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27791928185931333131885621 2605493267431062481114277)
                      ·
                        rfl

theorem cell23_5074180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_5074180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074180 prefixEnd_5074180 := by exact prefixLift 5074180
  have htrace : WordTrace (prefixWord ++ tailWord_5074180) baseStart_5074180 baseEnd_5074180 := by
    simpa [prefixWord, tailWord_5074180, baseEnd_5074180] using wordTrace_append hprefix tailTrace_5074180
  have hstable : (prefixWord ++ tailWord_5074180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074180).length < 2 ^ (prefixWord ++ tailWord_5074180).sum := by decide
  have hdescent : baseEnd_5074180 < baseStart_5074180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074203 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 7, 2]
def baseStart_5074203 : Nat := 118140960795 + 5074203 * 2 ^ 59
def prefixEnd_5074203 : Nat := 4983230072969 + 3 ^ 40 * 5074203 * 2
def baseEnd_5074203 : Nat := 2605505077486115891126671

theorem tailTrace_5074203 : CollatzResearch.WordTrace tailWord_5074203 prefixEnd_5074203 2605505077486115891126671 := by
  unfold tailWord_5074203
  simp only [CollatzResearch.WordTrace]
  refine ⟨185071387636036610723571263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123380925090691073815714175 185071387636036610723571263)
  ·
    refine ⟨277607081454054916085356895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185071387636036610723571263 277607081454054916085356895)
    ·
      refine ⟨416410622181082374128035343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277607081454054916085356895 416410622181082374128035343)
      ·
        refine ⟨624615933271623561192053015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416410622181082374128035343 624615933271623561192053015)
        ·
          refine ⟨936923899907435341788079523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624615933271623561192053015 936923899907435341788079523)
          ·
            refine ⟨1405385849861153012682119285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936923899907435341788079523 1405385849861153012682119285)
            ·
              refine ⟨131754923424483094938948683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1405385849861153012682119285 131754923424483094938948683)
              ·
                refine ⟨197632385136724642408423025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131754923424483094938948683 197632385136724642408423025)
                ·
                  refine ⟨148224288852543481806317269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197632385136724642408423025 148224288852543481806317269)
                  ·
                    refine ⟨3474006769981487854835561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 148224288852543481806317269 3474006769981487854835561)
                    ·
                      refine ⟨2605505077486115891126671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474006769981487854835561 2605505077486115891126671)
                      ·
                        rfl

theorem cell23_5074203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7, 2].length) (baseStart_5074203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074203 prefixEnd_5074203 := by exact prefixLift 5074203
  have htrace : WordTrace (prefixWord ++ tailWord_5074203) baseStart_5074203 baseEnd_5074203 := by
    simpa [prefixWord, tailWord_5074203, baseEnd_5074203] using wordTrace_append hprefix tailTrace_5074203
  have hstable : (prefixWord ++ tailWord_5074203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074203).length < 2 ^ (prefixWord ++ tailWord_5074203).sum := by decide
  have hdescent : baseEnd_5074203 < baseStart_5074203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074244 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_5074244 : Nat := 118140960795 + 5074244 * 2 ^ 59
def prefixEnd_5074244 : Nat := 4983230072969 + 3 ^ 40 * 5074244 * 2
def baseEnd_5074244 : Nat := 2605526130192950230713983

theorem tailTrace_5074244 : CollatzResearch.WordTrace tailWord_5074244 prefixEnd_5074244 2605526130192950230713983 := by
  unfold tailWord_5074244
  simp only [CollatzResearch.WordTrace]
  refine ⟨92536441514444037362906893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123381922019258716483875857 92536441514444037362906893)
  ·
    refine ⟨34701165567916514011090085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92536441514444037362906893 34701165567916514011090085)
    ·
      refine ⟨6506468543984346377079391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34701165567916514011090085 6506468543984346377079391)
      ·
        refine ⟨9759702815976519565619087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506468543984346377079391 9759702815976519565619087)
        ·
          refine ⟨14639554223964779348428631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9759702815976519565619087 14639554223964779348428631)
          ·
            refine ⟨21959331335947169022642947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14639554223964779348428631 21959331335947169022642947)
            ·
              refine ⟨32938997003920753533964421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21959331335947169022642947 32938997003920753533964421)
              ·
                refine ⟨6176061938235141287618329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32938997003920753533964421 6176061938235141287618329)
                ·
                  refine ⟨4632046453676355965713747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6176061938235141287618329 4632046453676355965713747)
                  ·
                    refine ⟨6948069680514533948570621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4632046453676355965713747 6948069680514533948570621)
                    ·
                      refine ⟨2605526130192950230713983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6948069680514533948570621 2605526130192950230713983)
                      ·
                        rfl

theorem cell23_5074244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_5074244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074244 prefixEnd_5074244 := by exact prefixLift 5074244
  have htrace : WordTrace (prefixWord ++ tailWord_5074244) baseStart_5074244 baseEnd_5074244 := by
    simpa [prefixWord, tailWord_5074244, baseEnd_5074244] using wordTrace_append hprefix tailTrace_5074244
  have hstable : (prefixWord ++ tailWord_5074244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074244).length < 2 ^ (prefixWord ++ tailWord_5074244).sum := by decide
  have hdescent : baseEnd_5074244 < baseStart_5074244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074263 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_5074263 : Nat := 118140960795 + 5074263 * 2 ^ 59
def prefixEnd_5074263 : Nat := 4983230072969 + 3 ^ 40 * 5074263 * 2
def baseEnd_5074263 : Nat := 2605535886325385656376395

theorem tailTrace_5074263 : CollatzResearch.WordTrace tailWord_5074263 prefixEnd_5074263 2605535886325385656376395 := by
  unfold tailWord_5074263
  simp only [CollatzResearch.WordTrace]
  refine ⟨185073576015819240970755443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123382384010546160647170295 185073576015819240970755443)
  ·
    refine ⟨277610364023728861456133165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185073576015819240970755443 277610364023728861456133165)
    ·
      refine ⟨104103886508898323046049937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277610364023728861456133165 104103886508898323046049937)
      ·
        refine ⟨78077914881673742284537453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104103886508898323046049937 78077914881673742284537453)
        ·
          refine ⟨29279218080627653356701545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78077914881673742284537453 29279218080627653356701545)
          ·
            refine ⟨21959413560470740017526159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29279218080627653356701545 21959413560470740017526159)
            ·
              refine ⟨32939120340706110026289239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21959413560470740017526159 32939120340706110026289239)
              ·
                refine ⟨49408680511059165039433859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32939120340706110026289239 49408680511059165039433859)
                ·
                  refine ⟨74113020766588747559150789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49408680511059165039433859 74113020766588747559150789)
                  ·
                    refine ⟨13896191393735390167340773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74113020766588747559150789 13896191393735390167340773)
                    ·
                      refine ⟨2605535886325385656376395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13896191393735390167340773 2605535886325385656376395)
                      ·
                        rfl

theorem cell23_5074263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_5074263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074263 prefixEnd_5074263 := by exact prefixLift 5074263
  have htrace : WordTrace (prefixWord ++ tailWord_5074263) baseStart_5074263 baseEnd_5074263 := by
    simpa [prefixWord, tailWord_5074263, baseEnd_5074263] using wordTrace_append hprefix tailTrace_5074263
  have hstable : (prefixWord ++ tailWord_5074263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074263).length < 2 ^ (prefixWord ++ tailWord_5074263).sum := by decide
  have hdescent : baseEnd_5074263 < baseStart_5074263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074283 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 3]
def baseStart_5074283 : Nat := 118140960795 + 5074283 * 2 ^ 59
def prefixEnd_5074283 : Nat := 4983230072969 + 3 ^ 40 * 5074283 * 2
def baseEnd_5074283 : Nat := 2605546155938475578126303

theorem tailTrace_5074283 : CollatzResearch.WordTrace tailWord_5074283 prefixEnd_5074283 2605546155938475578126303 := by
  unfold tailWord_5074283
  simp only [CollatzResearch.WordTrace]
  refine ⟨185074305475746784386483503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123382870317164522924322335 185074305475746784386483503)
  ·
    refine ⟨277611458213620176579725255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185074305475746784386483503 277611458213620176579725255)
    ·
      refine ⟨416417187320430264869587883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277611458213620176579725255 416417187320430264869587883)
      ·
        refine ⟨624625780980645397304381825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416417187320430264869587883 624625780980645397304381825)
        ·
          refine ⟨468469335735484047978286369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624625780980645397304381825 468469335735484047978286369)
          ·
            refine ⟨351352001801613035983714777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468469335735484047978286369 351352001801613035983714777)
            ·
              refine ⟨263514001351209776987786083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351352001801613035983714777 263514001351209776987786083)
              ·
                refine ⟨395271002026814665481679125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263514001351209776987786083 395271002026814665481679125)
                ·
                  refine ⟨18528328220006937444453709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 395271002026814665481679125 18528328220006937444453709)
                  ·
                    refine ⟨6948123082502601541670141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18528328220006937444453709 6948123082502601541670141)
                    ·
                      refine ⟨2605546155938475578126303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6948123082502601541670141 2605546155938475578126303)
                      ·
                        rfl

theorem cell23_5074283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 3].length) (baseStart_5074283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074283 prefixEnd_5074283 := by exact prefixLift 5074283
  have htrace : WordTrace (prefixWord ++ tailWord_5074283) baseStart_5074283 baseEnd_5074283 := by
    simpa [prefixWord, tailWord_5074283, baseEnd_5074283] using wordTrace_append hprefix tailTrace_5074283
  have hstable : (prefixWord ++ tailWord_5074283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074283).length < 2 ^ (prefixWord ++ tailWord_5074283).sum := by decide
  have hdescent : baseEnd_5074283 < baseStart_5074283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074318 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5074318 : Nat := 118140960795 + 5074318 * 2 ^ 59
def prefixEnd_5074318 : Nat := 4983230072969 + 3 ^ 40 * 5074318 * 2
def baseEnd_5074318 : Nat := 2605564127761382941188643

theorem tailTrace_5074318 : CollatzResearch.WordTrace tailWord_5074318 prefixEnd_5074318 2605564127761382941188643 := by
  unfold tailWord_5074318
  simp only [CollatzResearch.WordTrace]
  refine ⟨23134447753827498170500951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123383721353746656909338405 23134447753827498170500951)
  ·
    refine ⟨34701671630741247255751427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23134447753827498170500951 34701671630741247255751427)
    ·
      refine ⟨52052507446111870883627141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34701671630741247255751427 52052507446111870883627141)
      ·
        refine ⟨9759845146145975790680089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52052507446111870883627141 9759845146145975790680089)
        ·
          refine ⟨7319883859609481843010067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9759845146145975790680089 7319883859609481843010067)
          ·
            refine ⟨10979825789414222764515101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7319883859609481843010067 10979825789414222764515101)
            ·
              refine ⟨4117434671030333536693163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10979825789414222764515101 4117434671030333536693163)
              ·
                refine ⟨6176152006545500305039745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4117434671030333536693163 6176152006545500305039745)
                ·
                  refine ⟨4632114004909125228779809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6176152006545500305039745 4632114004909125228779809)
                  ·
                    refine ⟨3474085503681843921584857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4632114004909125228779809 3474085503681843921584857)
                    ·
                      refine ⟨2605564127761382941188643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474085503681843921584857 2605564127761382941188643)
                      ·
                        rfl

theorem cell23_5074318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5074318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074318 prefixEnd_5074318 := by exact prefixLift 5074318
  have htrace : WordTrace (prefixWord ++ tailWord_5074318) baseStart_5074318 baseEnd_5074318 := by
    simpa [prefixWord, tailWord_5074318, baseEnd_5074318] using wordTrace_append hprefix tailTrace_5074318
  have hstable : (prefixWord ++ tailWord_5074318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074318).length < 2 ^ (prefixWord ++ tailWord_5074318).sum := by decide
  have hdescent : baseEnd_5074318 < baseStart_5074318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074340 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_5074340 : Nat := 118140960795 + 5074340 * 2 ^ 59
def prefixEnd_5074340 : Nat := 4983230072969 + 3 ^ 40 * 5074340 * 2
def baseEnd_5074340 : Nat := 2605575424335781855113541

theorem tailTrace_5074340 : CollatzResearch.WordTrace tailWord_5074340 prefixEnd_5074340 2605575424335781855113541 := by
  unfold tailWord_5074340
  simp only [CollatzResearch.WordTrace]
  refine ⟨92538192218270141560654237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123384256291026855414205649 92538192218270141560654237)
  ·
    refine ⟨34701822081851303085245339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92538192218270141560654237 34701822081851303085245339)
    ·
      refine ⟨52052733122776954627868009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34701822081851303085245339 52052733122776954627868009)
      ·
        refine ⟨39039549842082715970901007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52052733122776954627868009 39039549842082715970901007)
        ·
          refine ⟨58559324763124073956351511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39039549842082715970901007 58559324763124073956351511)
          ·
            refine ⟨87838987144686110934527267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58559324763124073956351511 87838987144686110934527267)
            ·
              refine ⟨131758480717029166401790901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87838987144686110934527267 131758480717029166401790901)
              ·
                refine ⟨12352357567221484350167897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131758480717029166401790901 12352357567221484350167897)
                ·
                  refine ⟨9264268175416113262625923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12352357567221484350167897 9264268175416113262625923)
                  ·
                    refine ⟨13896402263124169893938885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9264268175416113262625923 13896402263124169893938885)
                    ·
                      refine ⟨2605575424335781855113541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13896402263124169893938885 2605575424335781855113541)
                      ·
                        rfl

theorem cell23_5074340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_5074340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074340 prefixEnd_5074340 := by exact prefixLift 5074340
  have htrace : WordTrace (prefixWord ++ tailWord_5074340) baseStart_5074340 baseEnd_5074340 := by
    simpa [prefixWord, tailWord_5074340, baseEnd_5074340] using wordTrace_append hprefix tailTrace_5074340
  have hstable : (prefixWord ++ tailWord_5074340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074340).length < 2 ^ (prefixWord ++ tailWord_5074340).sum := by decide
  have hdescent : baseEnd_5074340 < baseStart_5074340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074357 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5074357 : Nat := 118140960795 + 5074357 * 2 ^ 59
def prefixEnd_5074357 : Nat := 4983230072969 + 3 ^ 40 * 5074357 * 2
def baseEnd_5074357 : Nat := 2605584153506908288600963

theorem tailTrace_5074357 : CollatzResearch.WordTrace tailWord_5074357 prefixEnd_5074357 2605584153506908288600963 := by
  unfold tailWord_5074357
  simp only [CollatzResearch.WordTrace]
  refine ⟨185077004477478695024677325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123384669651652463349784883 185077004477478695024677325)
  ·
    refine ⟨69403876679054510634253997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185077004477478695024677325 69403876679054510634253997)
    ·
      refine ⟨26026453754645441487845249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69403876679054510634253997 26026453754645441487845249)
      ·
        refine ⟨19519840315984081115883937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26026453754645441487845249 19519840315984081115883937)
        ·
          refine ⟨14639880236988060836912953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19519840315984081115883937 14639880236988060836912953)
          ·
            refine ⟨10979910177741045627684715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14639880236988060836912953 10979910177741045627684715)
            ·
              refine ⟨16469865266611568441527073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10979910177741045627684715 16469865266611568441527073)
              ·
                refine ⟨12352398949958676331145305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16469865266611568441527073 12352398949958676331145305)
                ·
                  refine ⟨9264299212469007248358979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12352398949958676331145305 9264299212469007248358979)
                  ·
                    refine ⟨13896448818703510872538469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9264299212469007248358979 13896448818703510872538469)
                    ·
                      refine ⟨2605584153506908288600963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13896448818703510872538469 2605584153506908288600963)
                      ·
                        rfl

theorem cell23_5074357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5074357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074357 prefixEnd_5074357 := by exact prefixLift 5074357
  have htrace : WordTrace (prefixWord ++ tailWord_5074357) baseStart_5074357 baseEnd_5074357 := by
    simpa [prefixWord, tailWord_5074357, baseEnd_5074357] using wordTrace_append hprefix tailTrace_5074357
  have hstable : (prefixWord ++ tailWord_5074357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074357).length < 2 ^ (prefixWord ++ tailWord_5074357).sum := by decide
  have hdescent : baseEnd_5074357 < baseStart_5074357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074360 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_5074360 : Nat := 118140960795 + 5074360 * 2 ^ 59
def prefixEnd_5074360 : Nat := 4983230072969 + 3 ^ 40 * 5074360 * 2
def baseEnd_5074360 : Nat := 2605585693948871776863449

theorem tailTrace_5074360 : CollatzResearch.WordTrace tailWord_5074360 prefixEnd_5074360 2605585693948871776863449 := by
  unfold tailWord_5074360
  simp only [CollatzResearch.WordTrace]
  refine ⟨92538556948233913268518267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123384742597645217691357689 92538556948233913268518267)
  ·
    refine ⟨138807835422350869902777401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92538556948233913268518267 138807835422350869902777401)
    ·
      refine ⟨104105876566763152427083051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138807835422350869902777401 104105876566763152427083051)
      ·
        refine ⟨156158814850144728640624577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104105876566763152427083051 156158814850144728640624577)
        ·
          refine ⟨117119111137608546480468433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156158814850144728640624577 117119111137608546480468433)
          ·
            refine ⟨87839333353206409860351325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117119111137608546480468433 87839333353206409860351325)
            ·
              refine ⟨32939750007452403697631747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87839333353206409860351325 32939750007452403697631747)
              ·
                refine ⟨49409625011178605546447621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32939750007452403697631747 49409625011178605546447621)
                ·
                  refine ⟨9264304689595988539958929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49409625011178605546447621 9264304689595988539958929)
                  ·
                    refine ⟨6948228517196991404969197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9264304689595988539958929 6948228517196991404969197)
                    ·
                      refine ⟨2605585693948871776863449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6948228517196991404969197 2605585693948871776863449)
                      ·
                        rfl

theorem cell23_5074360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_5074360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074360 prefixEnd_5074360 := by exact prefixLift 5074360
  have htrace : WordTrace (prefixWord ++ tailWord_5074360) baseStart_5074360 baseEnd_5074360 := by
    simpa [prefixWord, tailWord_5074360, baseEnd_5074360] using wordTrace_append hprefix tailTrace_5074360
  have hstable : (prefixWord ++ tailWord_5074360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074360).length < 2 ^ (prefixWord ++ tailWord_5074360).sum := by decide
  have hdescent : baseEnd_5074360 < baseStart_5074360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074367 : List Nat := [1, 1, 2, 2, 2, 1, 1, 8, 1, 4]
def baseStart_5074367 : Nat := 118140960795 + 5074367 * 2 ^ 59
def prefixEnd_5074367 : Nat := 4983230072969 + 3 ^ 40 * 5074367 * 2
def baseEnd_5074367 : Nat := 868529762771151083158639

theorem tailTrace_5074367 : CollatzResearch.WordTrace tailWord_5074367 prefixEnd_5074367 868529762771151083158639 := by
  unfold tailWord_5074367
  simp only [CollatzResearch.WordTrace]
  refine ⟨185077369207442466732541355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123384912804961644488360903 185077369207442466732541355)
  ·
    refine ⟨277616053811163700098812033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185077369207442466732541355 277616053811163700098812033)
    ·
      refine ⟨208212040358372775074109025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277616053811163700098812033 208212040358372775074109025)
      ·
        refine ⟨156159030268779581305581769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208212040358372775074109025 156159030268779581305581769)
        ·
          refine ⟨117119272701584685979186327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156159030268779581305581769 117119272701584685979186327)
          ·
            refine ⟨175678909052377028968779491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117119272701584685979186327 175678909052377028968779491)
            ·
              refine ⟨263518363578565543453169237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175678909052377028968779491 263518363578565543453169237)
              ·
                refine ⟨3088105823186314962341827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 263518363578565543453169237 3088105823186314962341827)
                ·
                  refine ⟨4632158734779472443512741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088105823186314962341827 4632158734779472443512741)
                  ·
                    refine ⟨868529762771151083158639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632158734779472443512741 868529762771151083158639)
                    ·
                      rfl

theorem cell23_5074367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 4].length) (baseStart_5074367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074367 prefixEnd_5074367 := by exact prefixLift 5074367
  have htrace : WordTrace (prefixWord ++ tailWord_5074367) baseStart_5074367 baseEnd_5074367 := by
    simpa [prefixWord, tailWord_5074367, baseEnd_5074367] using wordTrace_append hprefix tailTrace_5074367
  have hstable : (prefixWord ++ tailWord_5074367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074367).length < 2 ^ (prefixWord ++ tailWord_5074367).sum := by decide
  have hdescent : baseEnd_5074367 < baseStart_5074367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074383 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_5074383 : Nat := 118140960795 + 5074383 * 2 ^ 59
def prefixEnd_5074383 : Nat := 4983230072969 + 3 ^ 40 * 5074383 * 2
def baseEnd_5074383 : Nat := 2605597504003925186875843

theorem tailTrace_5074383 : CollatzResearch.WordTrace tailWord_5074383 prefixEnd_5074383 2605597504003925186875843 := by
  unfold tailWord_5074383
  simp only [CollatzResearch.WordTrace]
  refine ⟨185077952775384501465123803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123385301850256334310082535 185077952775384501465123803)
  ·
    refine ⟨277616929163076752197685705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185077952775384501465123803 277616929163076752197685705)
    ·
      refine ⟨208212696872307564148264279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277616929163076752197685705 208212696872307564148264279)
      ·
        refine ⟨312319045308461346222396419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208212696872307564148264279 312319045308461346222396419)
        ·
          refine ⟨468478567962692019333594629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312319045308461346222396419 468478567962692019333594629)
          ·
            refine ⟨87839731493004753625048993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 468478567962692019333594629 87839731493004753625048993)
            ·
              refine ⟨65879798619753565218786745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87839731493004753625048993 65879798619753565218786745)
              ·
                refine ⟨49409848964815173914090059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65879798619753565218786745 49409848964815173914090059)
                ·
                  refine ⟨74114773447222760871135089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49409848964815173914090059 74114773447222760871135089)
                  ·
                    refine ⟨55586080085417070653351317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74114773447222760871135089 55586080085417070653351317)
                    ·
                      refine ⟨2605597504003925186875843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55586080085417070653351317 2605597504003925186875843)
                      ·
                        rfl

theorem cell23_5074383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_5074383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074383 prefixEnd_5074383 := by exact prefixLift 5074383
  have htrace : WordTrace (prefixWord ++ tailWord_5074383) baseStart_5074383 baseEnd_5074383 := by
    simpa [prefixWord, tailWord_5074383, baseEnd_5074383] using wordTrace_append hprefix tailTrace_5074383
  have hstable : (prefixWord ++ tailWord_5074383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074383).length < 2 ^ (prefixWord ++ tailWord_5074383).sum := by decide
  have hdescent : baseEnd_5074383 < baseStart_5074383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074418 : List Nat := [3, 2, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_5074418 : Nat := 118140960795 + 5074418 * 2 ^ 59
def prefixEnd_5074418 : Nat := 4983230072969 + 3 ^ 40 * 5074418 * 2
def baseEnd_5074418 : Nat := 868538491942277516646061

theorem tailTrace_5074418 : CollatzResearch.WordTrace tailWord_5074418 prefixEnd_5074418 868538491942277516646061 := by
  unfold tailWord_5074418
  simp only [CollatzResearch.WordTrace]
  refine ⟨46269807332564425610661977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123386152886838468295098605 46269807332564425610661977)
  ·
    refine ⟨34702355499423319207996483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46269807332564425610661977 34702355499423319207996483)
    ·
      refine ⟨52053533249134978811994725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34702355499423319207996483 52053533249134978811994725)
      ·
        refine ⟨9760037484212808527249011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52053533249134978811994725 9760037484212808527249011)
        ·
          refine ⟨14640056226319212790873517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9760037484212808527249011 14640056226319212790873517)
          ·
            refine ⟨5490021084869704796577569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14640056226319212790873517 5490021084869704796577569)
            ·
              refine ⟨4117515813652278597433177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490021084869704796577569 4117515813652278597433177)
              ·
                refine ⟨3088136860239208948074883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4117515813652278597433177 3088136860239208948074883)
                ·
                  refine ⟨4632205290358813422112325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088136860239208948074883 4632205290358813422112325)
                  ·
                    refine ⟨868538491942277516646061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632205290358813422112325 868538491942277516646061)
                    ·
                      rfl

theorem cell23_5074418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_5074418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074418 prefixEnd_5074418 := by exact prefixLift 5074418
  have htrace : WordTrace (prefixWord ++ tailWord_5074418) baseStart_5074418 baseEnd_5074418 := by
    simpa [prefixWord, tailWord_5074418, baseEnd_5074418] using wordTrace_append hprefix tailTrace_5074418
  have hstable : (prefixWord ++ tailWord_5074418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074418).length < 2 ^ (prefixWord ++ tailWord_5074418).sum := by decide
  have hdescent : baseEnd_5074418 < baseStart_5074418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074440 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 1, 6]
def baseStart_5074440 : Nat := 118140960795 + 5074440 * 2 ^ 59
def prefixEnd_5074440 : Nat := 4983230072969 + 3 ^ 40 * 5074440 * 2
def baseEnd_5074440 : Nat := 868542257467077154621027

theorem tailTrace_5074440 : CollatzResearch.WordTrace tailWord_5074440 prefixEnd_5074440 868542257467077154621027 := by
  unfold tailWord_5074440
  simp only [CollatzResearch.WordTrace]
  refine ⟨92540015868089000099974387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123386687824118666799965849 92540015868089000099974387)
  ·
    refine ⟨138810023802133500149961581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92540015868089000099974387 138810023802133500149961581)
    ·
      refine ⟨52053758925800062556235593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138810023802133500149961581 52053758925800062556235593)
      ·
        refine ⟨39040319194350046917176695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52053758925800062556235593 39040319194350046917176695)
        ·
          refine ⟨58560478791525070375765043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39040319194350046917176695 58560478791525070375765043)
          ·
            refine ⟨87840718187287605563647565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58560478791525070375765043 87840718187287605563647565)
            ·
              refine ⟨32940269320232852086367837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87840718187287605563647565 32940269320232852086367837)
              ·
                refine ⟨12352600995087319532387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32940269320232852086367837 12352600995087319532387939)
                ·
                  refine ⟨18528901492630979298581909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12352600995087319532387939 18528901492630979298581909)
                  ·
                    refine ⟨868542257467077154621027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18528901492630979298581909 868542257467077154621027)
                    ·
                      rfl

theorem cell23_5074440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_5074440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074440 prefixEnd_5074440 := by exact prefixLift 5074440
  have htrace : WordTrace (prefixWord ++ tailWord_5074440) baseStart_5074440 baseEnd_5074440 := by
    simpa [prefixWord, tailWord_5074440, baseEnd_5074440] using wordTrace_append hprefix tailTrace_5074440
  have hstable : (prefixWord ++ tailWord_5074440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074440).length < 2 ^ (prefixWord ++ tailWord_5074440).sum := by decide
  have hdescent : baseEnd_5074440 < baseStart_5074440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074445 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5074445 : Nat := 118140960795 + 5074445 * 2 ^ 59
def prefixEnd_5074445 : Nat := 4983230072969 + 3 ^ 40 * 5074445 * 2
def baseEnd_5074445 : Nat := 2605629339804503944300559

theorem tailTrace_5074445 : CollatzResearch.WordTrace tailWord_5074445 prefixEnd_5074445 2605629339804503944300559 := by
  unfold tailWord_5074445
  simp only [CollatzResearch.WordTrace]
  refine ⟨185080214101159886053880789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123386809400773257369253859 185080214101159886053880789)
  ·
    refine ⟨4337817517995934829387831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 185080214101159886053880789 4337817517995934829387831)
    ·
      refine ⟨6506726276993902244081747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337817517995934829387831 6506726276993902244081747)
      ·
        refine ⟨9760089415490853366122621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506726276993902244081747 9760089415490853366122621)
        ·
          refine ⟨3660033530809070012295983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9760089415490853366122621 3660033530809070012295983)
          ·
            refine ⟨5490050296213605018443975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3660033530809070012295983 5490050296213605018443975)
            ·
              refine ⟨8235075444320407527665963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5490050296213605018443975 8235075444320407527665963)
              ·
                refine ⟨12352613166480611291498945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8235075444320407527665963 12352613166480611291498945)
                ·
                  refine ⟨9264459874860458468624209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12352613166480611291498945 9264459874860458468624209)
                  ·
                    refine ⟨6948344906145343851468157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9264459874860458468624209 6948344906145343851468157)
                    ·
                      refine ⟨2605629339804503944300559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6948344906145343851468157 2605629339804503944300559)
                      ·
                        rfl

theorem cell23_5074445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5074445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074445 prefixEnd_5074445 := by exact prefixLift 5074445
  have htrace : WordTrace (prefixWord ++ tailWord_5074445) baseStart_5074445 baseEnd_5074445 := by
    simpa [prefixWord, tailWord_5074445, baseEnd_5074445] using wordTrace_append hprefix tailTrace_5074445
  have hstable : (prefixWord ++ tailWord_5074445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074445).length < 2 ^ (prefixWord ++ tailWord_5074445).sum := by decide
  have hdescent : baseEnd_5074445 < baseStart_5074445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074464 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5074464 : Nat := 118140960795 + 5074464 * 2 ^ 59
def prefixEnd_5074464 : Nat := 4983230072969 + 3 ^ 40 * 5074464 * 2
def baseEnd_5074464 : Nat := 2605639095936939369962971

theorem tailTrace_5074464 : CollatzResearch.WordTrace tailWord_5074464 prefixEnd_5074464 2605639095936939369962971 := by
  unfold tailWord_5074464
  simp only [CollatzResearch.WordTrace]
  refine ⟨92540453544045526149411223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123387271392060701532548297 92540453544045526149411223)
  ·
    refine ⟨138810680316068289224116835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92540453544045526149411223 138810680316068289224116835)
    ·
      refine ⟨208216020474102433836175253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138810680316068289224116835 208216020474102433836175253)
      ·
        refine ⟨9760125959723551586070715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208216020474102433836175253 9760125959723551586070715)
        ·
          refine ⟨14640188939585327379106073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9760125959723551586070715 14640188939585327379106073)
          ·
            refine ⟨10980141704688995534329555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14640188939585327379106073 10980141704688995534329555)
            ·
              refine ⟨16470212557033493301494333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10980141704688995534329555 16470212557033493301494333)
              ·
                refine ⟨6176329708887559988060375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16470212557033493301494333 6176329708887559988060375)
                ·
                  refine ⟨9264494563331339982090563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6176329708887559988060375 9264494563331339982090563)
                  ·
                    refine ⟨13896741844997009973135845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9264494563331339982090563 13896741844997009973135845)
                    ·
                      refine ⟨2605639095936939369962971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13896741844997009973135845 2605639095936939369962971)
                      ·
                        rfl

theorem cell23_5074464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5074464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074464 prefixEnd_5074464 := by exact prefixLift 5074464
  have htrace : WordTrace (prefixWord ++ tailWord_5074464) baseStart_5074464 baseEnd_5074464 := by
    simpa [prefixWord, tailWord_5074464, baseEnd_5074464] using wordTrace_append hprefix tailTrace_5074464
  have hstable : (prefixWord ++ tailWord_5074464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074464).length < 2 ^ (prefixWord ++ tailWord_5074464).sum := by decide
  have hdescent : baseEnd_5074464 < baseStart_5074464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074514 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_5074514 : Nat := 118140960795 + 5074514 * 2 ^ 59
def prefixEnd_5074514 : Nat := 4983230072969 + 3 ^ 40 * 5074514 * 2
def baseEnd_5074514 : Nat := 2605664769969664174337741

theorem tailTrace_5074514 : CollatzResearch.WordTrace tailWord_5074514 prefixEnd_5074514 2605664769969664174337741 := by
  unfold tailWord_5074514
  simp only [CollatzResearch.WordTrace]
  refine ⟨46270682684477477709535649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123388487158606607225428397 46270682684477477709535649)
  ·
    refine ⟨34703012013358108282151737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46270682684477477709535649 34703012013358108282151737)
    ·
      refine ⟨26027259010018581211613803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34703012013358108282151737 26027259010018581211613803)
      ·
        refine ⟨39040888515027871817420705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26027259010018581211613803 39040888515027871817420705)
        ·
          refine ⟨29280666386270903863065529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39040888515027871817420705 29280666386270903863065529)
          ·
            refine ⟨21960499789703177897299147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29280666386270903863065529 21960499789703177897299147)
            ·
              refine ⟨32940749684554766845948721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21960499789703177897299147 32940749684554766845948721)
              ·
                refine ⟨24705562263416075134461541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32940749684554766845948721 24705562263416075134461541)
                ·
                  refine ⟨4632292924390514087711539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24705562263416075134461541 4632292924390514087711539)
                  ·
                    refine ⟨6948439386585771131567309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4632292924390514087711539 6948439386585771131567309)
                    ·
                      refine ⟨2605664769969664174337741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6948439386585771131567309 2605664769969664174337741)
                      ·
                        rfl

theorem cell23_5074514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_5074514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074514 prefixEnd_5074514 := by exact prefixLift 5074514
  have htrace : WordTrace (prefixWord ++ tailWord_5074514) baseStart_5074514 baseEnd_5074514 := by
    simpa [prefixWord, tailWord_5074514, baseEnd_5074514] using wordTrace_append hprefix tailTrace_5074514
  have hstable : (prefixWord ++ tailWord_5074514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074514).length < 2 ^ (prefixWord ++ tailWord_5074514).sum := by decide
  have hdescent : baseEnd_5074514 < baseStart_5074514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074518 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5074518 : Nat := 118140960795 + 5074518 * 2 ^ 59
def prefixEnd_5074518 : Nat := 4983230072969 + 3 ^ 40 * 5074518 * 2
def baseEnd_5074518 : Nat := 2605666823892282158687723

theorem tailTrace_5074518 : CollatzResearch.WordTrace tailWord_5074518 prefixEnd_5074518 2605666823892282158687723 := by
  unfold tailWord_5074518
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567679789368463720080513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123388584419930279680858805 11567679789368463720080513)
  ·
    refine ⟨8675759842026347790060385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11567679789368463720080513 8675759842026347790060385)
    ·
      refine ⟨6506819881519760842545289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8675759842026347790060385 6506819881519760842545289)
      ·
        refine ⟨4880114911139820631908967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6506819881519760842545289 4880114911139820631908967)
        ·
          refine ⟨7320172366709730947863451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4880114911139820631908967 7320172366709730947863451)
          ·
            refine ⟨10980258550064596421795177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7320172366709730947863451 10980258550064596421795177)
            ·
              refine ⟨8235193912548447316346383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10980258550064596421795177 8235193912548447316346383)
              ·
                refine ⟨12352790868822670974519575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8235193912548447316346383 12352790868822670974519575)
                ·
                  refine ⟨18529186303234006461779363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12352790868822670974519575 18529186303234006461779363)
                  ·
                    refine ⟨27793779454851009692669045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18529186303234006461779363 27793779454851009692669045)
                    ·
                      refine ⟨2605666823892282158687723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27793779454851009692669045 2605666823892282158687723)
                      ·
                        rfl

theorem cell23_5074518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5074518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074518 prefixEnd_5074518 := by exact prefixLift 5074518
  have htrace : WordTrace (prefixWord ++ tailWord_5074518) baseStart_5074518 baseEnd_5074518 := by
    simpa [prefixWord, tailWord_5074518, baseEnd_5074518] using wordTrace_append hprefix tailTrace_5074518
  have hstable : (prefixWord ++ tailWord_5074518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074518).length < 2 ^ (prefixWord ++ tailWord_5074518).sum := by decide
  have hdescent : baseEnd_5074518 < baseStart_5074518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074520 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_5074520 : Nat := 118140960795 + 5074520 * 2 ^ 59
def prefixEnd_5074520 : Nat := 4983230072969 + 3 ^ 40 * 5074520 * 2
def baseEnd_5074520 : Nat := 2605667850853591150862713

theorem tailTrace_5074520 : CollatzResearch.WordTrace tailWord_5074520 prefixEnd_5074520 2605667850853591150862713 := by
  unfold tailWord_5074520
  simp only [CollatzResearch.WordTrace]
  refine ⟨92541474787944086931430507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123388633050592115908574009 92541474787944086931430507)
  ·
    refine ⟨138812212181916130397145761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92541474787944086931430507 138812212181916130397145761)
    ·
      refine ⟨104109159136437097797859321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138812212181916130397145761 104109159136437097797859321)
      ·
        refine ⟨78081869352327823348394491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104109159136437097797859321 78081869352327823348394491)
        ·
          refine ⟨117122804028491735022591737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78081869352327823348394491 117122804028491735022591737)
          ·
            refine ⟨87842103021368801266943803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117122804028491735022591737 87842103021368801266943803)
            ·
              refine ⟨131763154532053201900415705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87842103021368801266943803 131763154532053201900415705)
              ·
                refine ⟨98822365899039901425311779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131763154532053201900415705 98822365899039901425311779)
                ·
                  refine ⟨148233548848559852137967669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98822365899039901425311779 148233548848559852137967669)
                  ·
                    refine ⟨13896895204552486137934469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148233548848559852137967669 13896895204552486137934469)
                    ·
                      refine ⟨2605667850853591150862713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13896895204552486137934469 2605667850853591150862713)
                      ·
                        rfl

theorem cell23_5074520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_5074520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074520 prefixEnd_5074520 := by exact prefixLift 5074520
  have htrace : WordTrace (prefixWord ++ tailWord_5074520) baseStart_5074520 baseEnd_5074520 := by
    simpa [prefixWord, tailWord_5074520, baseEnd_5074520] using wordTrace_append hprefix tailTrace_5074520
  have hstable : (prefixWord ++ tailWord_5074520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074520).length < 2 ^ (prefixWord ++ tailWord_5074520).sum := by decide
  have hdescent : baseEnd_5074520 < baseStart_5074520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074540 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_5074540 : Nat := 118140960795 + 5074540 * 2 ^ 59
def prefixEnd_5074540 : Nat := 4983230072969 + 3 ^ 40 * 5074540 * 2
def baseEnd_5074540 : Nat := 2605678120466681072612621

theorem tailTrace_5074540 : CollatzResearch.WordTrace tailWord_5074540 prefixEnd_5074540 2605678120466681072612621 := by
  unfold tailWord_5074540
  simp only [CollatzResearch.WordTrace]
  refine ⟨92541839517907858639294537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123389119357210478185726049 92541839517907858639294537)
  ·
    refine ⟨69406379638430893979470903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92541839517907858639294537 69406379638430893979470903)
    ·
      refine ⟨104109569457646340969206355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69406379638430893979470903 104109569457646340969206355)
      ·
        refine ⟨156164354186469511453809533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104109569457646340969206355 156164354186469511453809533)
        ·
          refine ⟨58561632819926066795178575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156164354186469511453809533 58561632819926066795178575)
          ·
            refine ⟨87842449229889100192767863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58561632819926066795178575 87842449229889100192767863)
            ·
              refine ⟨131763673844833650289151795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87842449229889100192767863 131763673844833650289151795)
              ·
                refine ⟨197645510767250475433727693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131763673844833650289151795 197645510767250475433727693)
                ·
                  refine ⟨74117066537718928287647885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197645510767250475433727693 74117066537718928287647885)
                  ·
                    refine ⟨27793899951644598107867957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74117066537718928287647885 27793899951644598107867957)
                    ·
                      refine ⟨2605678120466681072612621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27793899951644598107867957 2605678120466681072612621)
                      ·
                        rfl

theorem cell23_5074540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_5074540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074540 prefixEnd_5074540 := by exact prefixLift 5074540
  have htrace : WordTrace (prefixWord ++ tailWord_5074540) baseStart_5074540 baseEnd_5074540 := by
    simpa [prefixWord, tailWord_5074540, baseEnd_5074540] using wordTrace_append hprefix tailTrace_5074540
  have hstable : (prefixWord ++ tailWord_5074540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074540).length < 2 ^ (prefixWord ++ tailWord_5074540).sum := by decide
  have hdescent : baseEnd_5074540 < baseStart_5074540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074554 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2]
def baseStart_5074554 : Nat := 118140960795 + 5074554 * 2 ^ 59
def prefixEnd_5074554 : Nat := 4983230072969 + 3 ^ 40 * 5074554 * 2
def baseEnd_5074554 : Nat := 2605685309195844017837557

theorem tailTrace_5074554 : CollatzResearch.WordTrace tailWord_5074554 prefixEnd_5074554 2605685309195844017837557 := by
  unfold tailWord_5074554
  simp only [CollatzResearch.WordTrace]
  refine ⟨46271047414441249417399679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123389459771843331779732477 46271047414441249417399679)
  ·
    refine ⟨69406571121661874126099519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46271047414441249417399679 69406571121661874126099519)
    ·
      refine ⟨104109856682492811189149279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69406571121661874126099519 104109856682492811189149279)
      ·
        refine ⟨156164785023739216783723919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104109856682492811189149279 156164785023739216783723919)
        ·
          refine ⟨234247177535608825175585879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156164785023739216783723919 234247177535608825175585879)
          ·
            refine ⟨351370766303413237763378819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234247177535608825175585879 351370766303413237763378819)
            ·
              refine ⟨527056149455119856645068229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351370766303413237763378819 527056149455119856645068229)
              ·
                refine ⟨98823028022834973120950293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527056149455119856645068229 98823028022834973120950293)
                ·
                  refine ⟨4632329438570389365044545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98823028022834973120950293 4632329438570389365044545)
                  ·
                    refine ⟨3474247078927792023783409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4632329438570389365044545 3474247078927792023783409)
                    ·
                      refine ⟨2605685309195844017837557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474247078927792023783409 2605685309195844017837557)
                      ·
                        rfl

theorem cell23_5074554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_5074554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074554 prefixEnd_5074554 := by exact prefixLift 5074554
  have htrace : WordTrace (prefixWord ++ tailWord_5074554) baseStart_5074554 baseEnd_5074554 := by
    simpa [prefixWord, tailWord_5074554, baseEnd_5074554] using wordTrace_append hprefix tailTrace_5074554
  have hstable : (prefixWord ++ tailWord_5074554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074554).length < 2 ^ (prefixWord ++ tailWord_5074554).sum := by decide
  have hdescent : baseEnd_5074554 < baseStart_5074554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074557 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_5074557 : Nat := 118140960795 + 5074557 * 2 ^ 59
def prefixEnd_5074557 : Nat := 4983230072969 + 3 ^ 40 * 5074557 * 2
def baseEnd_5074557 : Nat := 2605686849637807506100043

theorem tailTrace_5074557 : CollatzResearch.WordTrace tailWord_5074557 prefixEnd_5074557 2605686849637807506100043 := by
  unfold tailWord_5074557
  simp only [CollatzResearch.WordTrace]
  refine ⟨185084299076754129181957925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123389532717836086121305283 185084299076754129181957925)
  ·
    refine ⟨34703306076891399221617111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185084299076754129181957925 34703306076891399221617111)
    ·
      refine ⟨52054959115337098832425667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34703306076891399221617111 52054959115337098832425667)
      ·
        refine ⟨78082438673005648248638501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52054959115337098832425667 78082438673005648248638501)
        ·
          refine ⟨14640457251188559046619719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78082438673005648248638501 14640457251188559046619719)
          ·
            refine ⟨21960685876782838569929579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14640457251188559046619719 21960685876782838569929579)
            ·
              refine ⟨32941028815174257854894369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21960685876782838569929579 32941028815174257854894369)
              ·
                refine ⟨24705771611380693391170777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32941028815174257854894369 24705771611380693391170777)
                ·
                  refine ⟨18529328708535520043378083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24705771611380693391170777 18529328708535520043378083)
                  ·
                    refine ⟨27793993062803280065067125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18529328708535520043378083 27793993062803280065067125)
                    ·
                      refine ⟨2605686849637807506100043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27793993062803280065067125 2605686849637807506100043)
                      ·
                        rfl

theorem cell23_5074557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_5074557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074557 prefixEnd_5074557 := by exact prefixLift 5074557
  have htrace : WordTrace (prefixWord ++ tailWord_5074557) baseStart_5074557 baseEnd_5074557 := by
    simpa [prefixWord, tailWord_5074557, baseEnd_5074557] using wordTrace_append hprefix tailTrace_5074557
  have hstable : (prefixWord ++ tailWord_5074557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074557).length < 2 ^ (prefixWord ++ tailWord_5074557).sum := by decide
  have hdescent : baseEnd_5074557 < baseStart_5074557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074560 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 9]
def baseStart_5074560 : Nat := 118140960795 + 5074560 * 2 ^ 59
def prefixEnd_5074560 : Nat := 4983230072969 + 3 ^ 40 * 5074560 * 2
def baseEnd_5074560 : Nat := 289520932231085666040281

theorem tailTrace_5074560 : CollatzResearch.WordTrace tailWord_5074560 prefixEnd_5074560 289520932231085666040281 := by
  unfold tailWord_5074560
  simp only [CollatzResearch.WordTrace]
  refine ⟨92542204247871630347158567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123389605663828840462878089 92542204247871630347158567)
  ·
    refine ⟨138813306371807445520737851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92542204247871630347158567 138813306371807445520737851)
    ·
      refine ⟨208219959557711168281106777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138813306371807445520737851 208219959557711168281106777)
      ·
        refine ⟨156164969668283376210830083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208219959557711168281106777 156164969668283376210830083)
        ·
          refine ⟨234247454502425064316245125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156164969668283376210830083 234247454502425064316245125)
          ·
            refine ⟨43921397719204699559295961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234247454502425064316245125 43921397719204699559295961)
            ·
              refine ⟨32941048289403524669471971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43921397719204699559295961 32941048289403524669471971)
              ·
                refine ⟨49411572434105287004207957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32941048289403524669471971 49411572434105287004207957)
                ·
                  refine ⟨289520932231085666040281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49411572434105287004207957 289520932231085666040281)
                  ·
                    rfl

theorem cell23_5074560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_5074560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074560 prefixEnd_5074560 := by exact prefixLift 5074560
  have htrace : WordTrace (prefixWord ++ tailWord_5074560) baseStart_5074560 baseEnd_5074560 := by
    simpa [prefixWord, tailWord_5074560, baseEnd_5074560] using wordTrace_append hprefix tailTrace_5074560
  have hstable : (prefixWord ++ tailWord_5074560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074560).length < 2 ^ (prefixWord ++ tailWord_5074560).sum := by decide
  have hdescent : baseEnd_5074560 < baseStart_5074560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074626 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5074626 : Nat := 118140960795 + 5074626 * 2 ^ 59
def prefixEnd_5074626 : Nat := 4983230072969 + 3 ^ 40 * 5074626 * 2
def baseEnd_5074626 : Nat := 2605722279802967736137227

theorem tailTrace_5074626 : CollatzResearch.WordTrace tailWord_5074626 prefixEnd_5074626 2605722279802967736137227 := by
  unfold tailWord_5074626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46271703928376038491554933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123391210475669435977479821 46271703928376038491554933)
  ·
    refine ⟨4337972243285253608583275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46271703928376038491554933 4337972243285253608583275)
    ·
      refine ⟨6506958364927880412874913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337972243285253608583275 6506958364927880412874913)
      ·
        refine ⟨4880218773695910309656185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6506958364927880412874913 4880218773695910309656185)
        ·
          refine ⟨3660164080271932732242139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4880218773695910309656185 3660164080271932732242139)
          ·
            refine ⟨5490246120407899098363209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3660164080271932732242139 5490246120407899098363209)
            ·
              refine ⟨4117684590305924323772407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490246120407899098363209 4117684590305924323772407)
              ·
                refine ⟨6176526885458886485658611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4117684590305924323772407 6176526885458886485658611)
                ·
                  refine ⟨9264790328188329728487917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6176526885458886485658611 9264790328188329728487917)
                  ·
                    refine ⟨3474296373070623648182969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9264790328188329728487917 3474296373070623648182969)
                    ·
                      refine ⟨2605722279802967736137227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474296373070623648182969 2605722279802967736137227)
                      ·
                        rfl

theorem cell23_5074626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5074626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074626 prefixEnd_5074626 := by exact prefixLift 5074626
  have htrace : WordTrace (prefixWord ++ tailWord_5074626) baseStart_5074626 baseEnd_5074626 := by
    simpa [prefixWord, tailWord_5074626, baseEnd_5074626] using wordTrace_append hprefix tailTrace_5074626
  have hstable : (prefixWord ++ tailWord_5074626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074626).length < 2 ^ (prefixWord ++ tailWord_5074626).sum := by decide
  have hdescent : baseEnd_5074626 < baseStart_5074626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074664 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_5074664 : Nat := 118140960795 + 5074664 * 2 ^ 59
def prefixEnd_5074664 : Nat := 4983230072969 + 3 ^ 40 * 5074664 * 2
def baseEnd_5074664 : Nat := 2605741792067838587462051

theorem tailTrace_5074664 : CollatzResearch.WordTrace tailWord_5074664 prefixEnd_5074664 2605741792067838587462051 := by
  unfold tailWord_5074664
  simp only [CollatzResearch.WordTrace]
  refine ⟨92544100843683243228051523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123392134458244324304068697 92544100843683243228051523)
  ·
    refine ⟨138816151265524864842077285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92544100843683243228051523 138816151265524864842077285)
    ·
      refine ⟨26028028362285912157889491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138816151265524864842077285 26028028362285912157889491)
      ·
        refine ⟨39042042543428868236834237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26028028362285912157889491 39042042543428868236834237)
        ·
          refine ⟨14640765953785825588812839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39042042543428868236834237 14640765953785825588812839)
          ·
            refine ⟨21961148930678738383219259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14640765953785825588812839 21961148930678738383219259)
            ·
              refine ⟨32941723396018107574828889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21961148930678738383219259 32941723396018107574828889)
              ·
                refine ⟨24706292547013580681121667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32941723396018107574828889 24706292547013580681121667)
                ·
                  refine ⟨37059438820520371021682501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24706292547013580681121667 37059438820520371021682501)
                  ·
                    refine ⟨6948644778847569566565469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37059438820520371021682501 6948644778847569566565469)
                    ·
                      refine ⟨2605741792067838587462051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6948644778847569566565469 2605741792067838587462051)
                      ·
                        rfl

theorem cell23_5074664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_5074664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074664 prefixEnd_5074664 := by exact prefixLift 5074664
  have htrace : WordTrace (prefixWord ++ tailWord_5074664) baseStart_5074664 baseEnd_5074664 := by
    simpa [prefixWord, tailWord_5074664, baseEnd_5074664] using wordTrace_append hprefix tailTrace_5074664
  have hstable : (prefixWord ++ tailWord_5074664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074664).length < 2 ^ (prefixWord ++ tailWord_5074664).sum := by decide
  have hdescent : baseEnd_5074664 < baseStart_5074664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074667 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 6]
def baseStart_5074667 : Nat := 118140960795 + 5074667 * 2 ^ 59
def prefixEnd_5074667 : Nat := 4983230072969 + 3 ^ 40 * 5074667 * 2
def baseEnd_5074667 : Nat := 289527036945533563969393

theorem tailTrace_5074667 : CollatzResearch.WordTrace tailWord_5074667 prefixEnd_5074667 289527036945533563969393 := by
  unfold tailWord_5074667
  simp only [CollatzResearch.WordTrace]
  refine ⟨185088311106355617968462255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123392207404237078645641503 185088311106355617968462255)
  ·
    refine ⟨277632466659533426952693383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185088311106355617968462255 277632466659533426952693383)
    ·
      refine ⟨416448699989300140429040075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277632466659533426952693383 416448699989300140429040075)
      ·
        refine ⟨624673049983950210643560113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416448699989300140429040075 624673049983950210643560113)
        ·
          refine ⟨468504787487962657982670085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624673049983950210643560113 468504787487962657982670085)
          ·
            refine ⟨87844647653992998371750641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 468504787487962657982670085 87844647653992998371750641)
            ·
              refine ⟨65883485740494748778812981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87844647653992998371750641 65883485740494748778812981)
              ·
                refine ⟨6176576788171382698013717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65883485740494748778812981 6176576788171382698013717)
                ·
                  refine ⟨289527036945533563969393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6176576788171382698013717 289527036945533563969393)
                  ·
                    rfl

theorem cell23_5074667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 6].length) (baseStart_5074667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074667 prefixEnd_5074667 := by exact prefixLift 5074667
  have htrace : WordTrace (prefixWord ++ tailWord_5074667) baseStart_5074667 baseEnd_5074667 := by
    simpa [prefixWord, tailWord_5074667, baseEnd_5074667] using wordTrace_append hprefix tailTrace_5074667
  have hstable : (prefixWord ++ tailWord_5074667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074667).length < 2 ^ (prefixWord ++ tailWord_5074667).sum := by decide
  have hdescent : baseEnd_5074667 < baseStart_5074667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074697 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 5, 5]
def baseStart_5074697 : Nat := 118140960795 + 5074697 * 2 ^ 59
def prefixEnd_5074697 : Nat := 4983230072969 + 3 ^ 40 * 5074697 * 2
def baseEnd_5074697 : Nat := 868586245643145652783133

theorem tailTrace_5074697 : CollatzResearch.WordTrace tailWord_5074697 prefixEnd_5074697 868586245643145652783133 := by
  unfold tailWord_5074697
  simp only [CollatzResearch.WordTrace]
  refine ⟨185089405296246933092054345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123392936864164622061369563 185089405296246933092054345)
  ·
    refine ⟨138817053972185199819040759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185089405296246933092054345 138817053972185199819040759)
    ·
      refine ⟨208225580958277799728561139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138817053972185199819040759 208225580958277799728561139)
      ·
        refine ⟨312338371437416699592841709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208225580958277799728561139 312338371437416699592841709)
        ·
          refine ⟨117126889289031262347315641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312338371437416699592841709 117126889289031262347315641)
          ·
            refine ⟨87845166966773446760486731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117126889289031262347315641 87845166966773446760486731)
            ·
              refine ⟨131767750450160170140730097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87845166966773446760486731 131767750450160170140730097)
              ·
                refine ⟨98825812837620127605547573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131767750450160170140730097 98825812837620127605547573)
                ·
                  refine ⟨9264919953526886963020085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98825812837620127605547573 9264919953526886963020085)
                  ·
                    refine ⟨868586245643145652783133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9264919953526886963020085 868586245643145652783133)
                    ·
                      rfl

theorem cell23_5074697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_5074697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074697 prefixEnd_5074697 := by exact prefixLift 5074697
  have htrace : WordTrace (prefixWord ++ tailWord_5074697) baseStart_5074697 baseEnd_5074697 := by
    simpa [prefixWord, tailWord_5074697, baseEnd_5074697] using wordTrace_append hprefix tailTrace_5074697
  have hstable : (prefixWord ++ tailWord_5074697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074697).length < 2 ^ (prefixWord ++ tailWord_5074697).sum := by decide
  have hdescent : baseEnd_5074697 < baseStart_5074697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074738 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_5074738 : Nat := 118140960795 + 5074738 * 2 ^ 59
def prefixEnd_5074738 : Nat := 4983230072969 + 3 ^ 40 * 5074738 * 2
def baseEnd_5074738 : Nat := 2605779789636271297936711

theorem tailTrace_5074738 : CollatzResearch.WordTrace tailWord_5074738 prefixEnd_5074738 2605779789636271297936711 := by
  unfold tailWord_5074738
  simp only [CollatzResearch.WordTrace]
  refine ⟨46272725172274599273574217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123393933792732264729531245 46272725172274599273574217)
  ·
    refine ⟨34704543879205949455180663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46272725172274599273574217 34704543879205949455180663)
    ·
      refine ⟨52056815818808924182770995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34704543879205949455180663 52056815818808924182770995)
      ·
        refine ⟨78085223728213386274156493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52056815818808924182770995 78085223728213386274156493)
        ·
          refine ⟨29281958898080019852808685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78085223728213386274156493 29281958898080019852808685)
          ·
            refine ⟨10980734586780007444803257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29281958898080019852808685 10980734586780007444803257)
            ·
              refine ⟨8235550940085005583602443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10980734586780007444803257 8235550940085005583602443)
              ·
                refine ⟨12353326410127508375403665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8235550940085005583602443 12353326410127508375403665)
                ·
                  refine ⟨9264994807595631281552749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12353326410127508375403665 9264994807595631281552749)
                  ·
                    refine ⟨3474373052848361730582281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9264994807595631281552749 3474373052848361730582281)
                    ·
                      refine ⟨2605779789636271297936711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474373052848361730582281 2605779789636271297936711)
                      ·
                        rfl

theorem cell23_5074738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_5074738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074738 prefixEnd_5074738 := by exact prefixLift 5074738
  have htrace : WordTrace (prefixWord ++ tailWord_5074738) baseStart_5074738 baseEnd_5074738 := by
    simpa [prefixWord, tailWord_5074738, baseEnd_5074738] using wordTrace_append hprefix tailTrace_5074738
  have hstable : (prefixWord ++ tailWord_5074738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074738).length < 2 ^ (prefixWord ++ tailWord_5074738).sum := by decide
  have hdescent : baseEnd_5074738 < baseStart_5074738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074744 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 1, 6]
def baseStart_5074744 : Nat := 118140960795 + 5074744 * 2 ^ 59
def prefixEnd_5074744 : Nat := 4983230072969 + 3 ^ 40 * 5074744 * 2
def baseEnd_5074744 : Nat := 868594290173399424820561

theorem tailTrace_5074744 : CollatzResearch.WordTrace tailWord_5074744 prefixEnd_5074744 868594290173399424820561 := by
  unfold tailWord_5074744
  simp only [CollatzResearch.WordTrace]
  refine ⟨92545559763538330059507643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123394079684717773412676857 92545559763538330059507643)
  ·
    refine ⟨138818339645307495089261465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92545559763538330059507643 138818339645307495089261465)
    ·
      refine ⟨104113754733980621316946099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138818339645307495089261465 104113754733980621316946099)
      ·
        refine ⟨156170632100970931975419149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104113754733980621316946099 156170632100970931975419149)
        ·
          refine ⟨58563987037864099490782181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156170632100970931975419149 58563987037864099490782181)
          ·
            refine ⟨10980747569599518654521659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58563987037864099490782181 10980747569599518654521659)
            ·
              refine ⟨16471121354399277981782489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10980747569599518654521659 16471121354399277981782489)
              ·
                refine ⟨12353341015799458486336867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16471121354399277981782489 12353341015799458486336867)
                ·
                  refine ⟨18530011523699187729505301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12353341015799458486336867 18530011523699187729505301)
                  ·
                    refine ⟨868594290173399424820561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18530011523699187729505301 868594290173399424820561)
                    ·
                      rfl

theorem cell23_5074744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_5074744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074744 prefixEnd_5074744 := by exact prefixLift 5074744
  have htrace : WordTrace (prefixWord ++ tailWord_5074744) baseStart_5074744 baseEnd_5074744 := by
    simpa [prefixWord, tailWord_5074744, baseEnd_5074744] using wordTrace_append hprefix tailTrace_5074744
  have hstable : (prefixWord ++ tailWord_5074744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074744).length < 2 ^ (prefixWord ++ tailWord_5074744).sum := by decide
  have hdescent : baseEnd_5074744 < baseStart_5074744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074761 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 2, 4]
def baseStart_5074761 : Nat := 118140960795 + 5074761 * 2 ^ 59
def prefixEnd_5074761 : Nat := 4983230072969 + 3 ^ 40 * 5074761 * 2
def baseEnd_5074761 : Nat := 868597199897108235983035

theorem tailTrace_5074761 : CollatzResearch.WordTrace tailWord_5074761 prefixEnd_5074761 868597199897108235983035 := by
  unfold tailWord_5074761
  simp only [CollatzResearch.WordTrace]
  refine ⟨185091739568015072022384137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123394493045343381348256091 185091739568015072022384137)
  ·
    refine ⟨138818804676011304016788103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185091739568015072022384137 138818804676011304016788103)
    ·
      refine ⟨208228207014016956025182155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138818804676011304016788103 208228207014016956025182155)
      ·
        refine ⟨312342310521025434037773233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208228207014016956025182155 312342310521025434037773233)
        ·
          refine ⟨234256732890769075528329925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312342310521025434037773233 234256732890769075528329925)
          ·
            refine ⟨43923137417019201661561861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234256732890769075528329925 43923137417019201661561861)
            ·
              refine ⟨8235588265691100311542849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43923137417019201661561861 8235588265691100311542849)
              ·
                refine ⟨6176691199268325233657137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8235588265691100311542849 6176691199268325233657137)
                ·
                  refine ⟨4632518399451243925242853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6176691199268325233657137 4632518399451243925242853)
                  ·
                    refine ⟨868597199897108235983035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632518399451243925242853 868597199897108235983035)
                    ·
                      rfl

theorem cell23_5074761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_5074761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074761 prefixEnd_5074761 := by exact prefixLift 5074761
  have htrace : WordTrace (prefixWord ++ tailWord_5074761) baseStart_5074761 baseEnd_5074761 := by
    simpa [prefixWord, tailWord_5074761, baseEnd_5074761] using wordTrace_append hprefix tailTrace_5074761
  have hstable : (prefixWord ++ tailWord_5074761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074761).length < 2 ^ (prefixWord ++ tailWord_5074761).sum := by decide
  have hdescent : baseEnd_5074761 < baseStart_5074761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074801 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_5074801 : Nat := 118140960795 + 5074801 * 2 ^ 59
def prefixEnd_5074801 : Nat := 4983230072969 + 3 ^ 40 * 5074801 * 2
def baseEnd_5074801 : Nat := 2605812138917504551448921

theorem tailTrace_5074801 : CollatzResearch.WordTrace tailWord_5074801 prefixEnd_5074801 2605812138917504551448921 := by
  unfold tailWord_5074801
  simp only [CollatzResearch.WordTrace]
  refine ⟨185093198487870158853840257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123395465658580105902560171 185093198487870158853840257)
  ·
    refine ⟨138819898865902619140380193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185093198487870158853840257 138819898865902619140380193)
    ·
      refine ⟨104114924149426964355285145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138819898865902619140380193 104114924149426964355285145)
      ·
        refine ⟨78086193112070223266463859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104114924149426964355285145 78086193112070223266463859)
        ·
          refine ⟨117129289668105334899695789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78086193112070223266463859 117129289668105334899695789)
          ·
            refine ⟨43923483625539500587385921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117129289668105334899695789 43923483625539500587385921)
            ·
              refine ⟨32942612719154625440539441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43923483625539500587385921 32942612719154625440539441)
              ·
                refine ⟨24706959539365969080404581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32942612719154625440539441 24706959539365969080404581)
                ·
                  refine ⟨4632554913631119202575859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24706959539365969080404581 4632554913631119202575859)
                  ·
                    refine ⟨6948832370446678803863789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4632554913631119202575859 6948832370446678803863789)
                    ·
                      refine ⟨2605812138917504551448921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6948832370446678803863789 2605812138917504551448921)
                      ·
                        rfl

theorem cell23_5074801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_5074801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074801 prefixEnd_5074801 := by exact prefixLift 5074801
  have htrace : WordTrace (prefixWord ++ tailWord_5074801) baseStart_5074801 baseEnd_5074801 := by
    simpa [prefixWord, tailWord_5074801, baseEnd_5074801] using wordTrace_append hprefix tailTrace_5074801
  have hstable : (prefixWord ++ tailWord_5074801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074801).length < 2 ^ (prefixWord ++ tailWord_5074801).sum := by decide
  have hdescent : baseEnd_5074801 < baseStart_5074801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074845 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_5074845 : Nat := 118140960795 + 5074845 * 2 ^ 59
def prefixEnd_5074845 : Nat := 4983230072969 + 3 ^ 40 * 5074845 * 2
def baseEnd_5074845 : Nat := 2605834732066302379298719

theorem tailTrace_5074845 : CollatzResearch.WordTrace tailWord_5074845 prefixEnd_5074845 2605834732066302379298719 := by
  unfold tailWord_5074845
  simp only [CollatzResearch.WordTrace]
  refine ⟨185094803299710754368441989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123396535533140502912294659 185094803299710754368441989)
  ·
    refine ⟨34705275618695766444082873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185094803299710754368441989 34705275618695766444082873)
    ·
      refine ⟨26028956714021824833062155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34705275618695766444082873 26028956714021824833062155)
      ·
        refine ⟨39043435071032737249593233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26028956714021824833062155 39043435071032737249593233)
        ·
          refine ⟨29282576303274552937194925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39043435071032737249593233 29282576303274552937194925)
          ·
            refine ⟨10980966113727957351448097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29282576303274552937194925 10980966113727957351448097)
            ·
              refine ⟨8235724585295968013586073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10980966113727957351448097 8235724585295968013586073)
              ·
                refine ⟨6176793438971976010189555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8235724585295968013586073 6176793438971976010189555)
                ·
                  refine ⟨9265190158457964015284333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6176793438971976010189555 9265190158457964015284333)
                  ·
                    refine ⟨3474446309421736505731625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9265190158457964015284333 3474446309421736505731625)
                    ·
                      refine ⟨2605834732066302379298719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474446309421736505731625 2605834732066302379298719)
                      ·
                        rfl

theorem cell23_5074845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_5074845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074845 prefixEnd_5074845 := by exact prefixLift 5074845
  have htrace : WordTrace (prefixWord ++ tailWord_5074845) baseStart_5074845 baseEnd_5074845 := by
    simpa [prefixWord, tailWord_5074845, baseEnd_5074845] using wordTrace_append hprefix tailTrace_5074845
  have hstable : (prefixWord ++ tailWord_5074845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074845).length < 2 ^ (prefixWord ++ tailWord_5074845).sum := by decide
  have hdescent : baseEnd_5074845 < baseStart_5074845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074892 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5074892 : Nat := 118140960795 + 5074892 * 2 ^ 59
def prefixEnd_5074892 : Nat := 4983230072969 + 3 ^ 40 * 5074892 * 2
def baseEnd_5074892 : Nat := 2605858865657063695411003

theorem tailTrace_5074892 : CollatzResearch.WordTrace tailWord_5074892 prefixEnd_5074892 2605858865657063695411003 := by
  unfold tailWord_5074892
  simp only [CollatzResearch.WordTrace]
  refine ⟨92548258765270240697701465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123397678353693654263601953 92548258765270240697701465)
  ·
    refine ⟨69411194073952680523276099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92548258765270240697701465 69411194073952680523276099)
    ·
      refine ⟨104116791110929020784914149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69411194073952680523276099 104116791110929020784914149)
      ·
        refine ⟨19521898333299191397171403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104116791110929020784914149 19521898333299191397171403)
        ·
          refine ⟨29282847499948787095757105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19521898333299191397171403 29282847499948787095757105)
          ·
            refine ⟨21962135624961590321817829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29282847499948787095757105 21962135624961590321817829)
            ·
              refine ⟨4117900429680298185340843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21962135624961590321817829 4117900429680298185340843)
              ·
                refine ⟨6176850644520447278011265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4117900429680298185340843 6176850644520447278011265)
                ·
                  refine ⟨4632637983390335458508449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6176850644520447278011265 4632637983390335458508449)
                  ·
                    refine ⟨3474478487542751593881337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4632637983390335458508449 3474478487542751593881337)
                    ·
                      refine ⟨2605858865657063695411003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474478487542751593881337 2605858865657063695411003)
                      ·
                        rfl

theorem cell23_5074892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5074892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074892 prefixEnd_5074892 := by exact prefixLift 5074892
  have htrace : WordTrace (prefixWord ++ tailWord_5074892) baseStart_5074892 baseEnd_5074892 := by
    simpa [prefixWord, tailWord_5074892, baseEnd_5074892] using wordTrace_append hprefix tailTrace_5074892
  have hstable : (prefixWord ++ tailWord_5074892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074892).length < 2 ^ (prefixWord ++ tailWord_5074892).sum := by decide
  have hdescent : baseEnd_5074892 < baseStart_5074892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074904 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_5074904 : Nat := 118140960795 + 5074904 * 2 ^ 59
def prefixEnd_5074904 : Nat := 4983230072969 + 3 ^ 40 * 5074904 * 2
def baseEnd_5074904 : Nat := 2605865027424917648460947

theorem tailTrace_5074904 : CollatzResearch.WordTrace tailWord_5074904 prefixEnd_5074904 2605865027424917648460947 := by
  unfold tailWord_5074904
  simp only [CollatzResearch.WordTrace]
  refine ⟨92548477603248503722419883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123397970137664671629893177 92548477603248503722419883)
  ·
    refine ⟨138822716404872755583629825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92548477603248503722419883 138822716404872755583629825)
    ·
      refine ⟨104117037303654566687722369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138822716404872755583629825 104117037303654566687722369)
      ·
        refine ⟨78087777977740925015791777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104117037303654566687722369 78087777977740925015791777)
        ·
          refine ⟨58565833483305693761843833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78087777977740925015791777 58565833483305693761843833)
          ·
            refine ⟨43924375112479270321382875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58565833483305693761843833 43924375112479270321382875)
            ·
              refine ⟨65886562668718905482074313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43924375112479270321382875 65886562668718905482074313)
              ·
                refine ⟨49414922001539179111555735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65886562668718905482074313 49414922001539179111555735)
                ·
                  refine ⟨74122383002308768667333603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49414922001539179111555735 74122383002308768667333603)
                  ·
                    refine ⟨111183574503463153001000405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74122383002308768667333603 111183574503463153001000405)
                    ·
                      refine ⟨2605865027424917648460947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111183574503463153001000405 2605865027424917648460947)
                      ·
                        rfl

theorem cell23_5074904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_5074904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074904 prefixEnd_5074904 := by exact prefixLift 5074904
  have htrace : WordTrace (prefixWord ++ tailWord_5074904) baseStart_5074904 baseEnd_5074904 := by
    simpa [prefixWord, tailWord_5074904, baseEnd_5074904] using wordTrace_append hprefix tailTrace_5074904
  have hstable : (prefixWord ++ tailWord_5074904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074904).length < 2 ^ (prefixWord ++ tailWord_5074904).sum := by decide
  have hdescent : baseEnd_5074904 < baseStart_5074904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074911 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 2, 5]
def baseStart_5074911 : Nat := 118140960795 + 5074911 * 2 ^ 59
def prefixEnd_5074911 : Nat := 4983230072969 + 3 ^ 40 * 5074911 * 2
def baseEnd_5074911 : Nat := 868622873929833040357805

theorem tailTrace_5074911 : CollatzResearch.WordTrace tailWord_5074911 prefixEnd_5074911 868622873929833040357805 := by
  unfold tailWord_5074911
  simp only [CollatzResearch.WordTrace]
  refine ⟨185097210517471647640344587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123398140344981098426896391 185097210517471647640344587)
  ·
    refine ⟨277645815776207471460516881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185097210517471647640344587 277645815776207471460516881)
    ·
      refine ⟨208234361832155603595387661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277645815776207471460516881 208234361832155603595387661)
      ·
        refine ⟨78087885687058351348270373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208234361832155603595387661 78087885687058351348270373)
        ·
          refine ⟨14641478566323440877800695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78087885687058351348270373 14641478566323440877800695)
          ·
            refine ⟨21962217849485161316701043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14641478566323440877800695 21962217849485161316701043)
            ·
              refine ⟨32943326774227741975051565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21962217849485161316701043 32943326774227741975051565)
              ·
                refine ⟨12353747540335403240644337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32943326774227741975051565 12353747540335403240644337)
                ·
                  refine ⟨9265310655251552430483253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12353747540335403240644337 9265310655251552430483253)
                  ·
                    refine ⟨868622873929833040357805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9265310655251552430483253 868622873929833040357805)
                    ·
                      rfl

theorem cell23_5074911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_5074911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074911 prefixEnd_5074911 := by exact prefixLift 5074911
  have htrace : WordTrace (prefixWord ++ tailWord_5074911) baseStart_5074911 baseEnd_5074911 := by
    simpa [prefixWord, tailWord_5074911, baseEnd_5074911] using wordTrace_append hprefix tailTrace_5074911
  have hstable : (prefixWord ++ tailWord_5074911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074911).length < 2 ^ (prefixWord ++ tailWord_5074911).sum := by decide
  have hdescent : baseEnd_5074911 < baseStart_5074911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074931 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 3, 6, 2]
def baseStart_5074931 : Nat := 118140960795 + 5074931 * 2 ^ 59
def prefixEnd_5074931 : Nat := 4983230072969 + 3 ^ 40 * 5074931 * 2
def baseEnd_5074931 : Nat := 2605878891402589042823323

theorem tailTrace_5074931 : CollatzResearch.WordTrace tailWord_5074931 prefixEnd_5074931 2605878891402589042823323 := by
  unfold tailWord_5074931
  simp only [CollatzResearch.WordTrace]
  refine ⟨185097939977399191056072647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123398626651599460704048431 185097939977399191056072647)
  ·
    refine ⟨277646909966098786584108971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185097939977399191056072647 277646909966098786584108971)
    ·
      refine ⟨416470364949148179876163457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277646909966098786584108971 416470364949148179876163457)
      ·
        refine ⟨312352773711861134907122593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416470364949148179876163457 312352773711861134907122593)
        ·
          refine ⟨234264580283895851180341945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312352773711861134907122593 234264580283895851180341945)
          ·
            refine ⟨175698435212921888385256459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234264580283895851180341945 175698435212921888385256459)
            ·
              refine ⟨263547652819382832577884689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175698435212921888385256459 263547652819382832577884689)
              ·
                refine ⟨197660739614537124433413517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263547652819382832577884689 197660739614537124433413517)
                ·
                  refine ⟨74122777355451421662530069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197660739614537124433413517 74122777355451421662530069)
                  ·
                    refine ⟨3474505188536785390431097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74122777355451421662530069 3474505188536785390431097)
                    ·
                      refine ⟨2605878891402589042823323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474505188536785390431097 2605878891402589042823323)
                      ·
                        rfl

theorem cell23_5074931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6, 2].length) (baseStart_5074931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074931 prefixEnd_5074931 := by exact prefixLift 5074931
  have htrace : WordTrace (prefixWord ++ tailWord_5074931) baseStart_5074931 baseEnd_5074931 := by
    simpa [prefixWord, tailWord_5074931, baseEnd_5074931] using wordTrace_append hprefix tailTrace_5074931
  have hstable : (prefixWord ++ tailWord_5074931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074931).length < 2 ^ (prefixWord ++ tailWord_5074931).sum := by decide
  have hdescent : baseEnd_5074931 < baseStart_5074931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074944 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_5074944 : Nat := 118140960795 + 5074944 * 2 ^ 59
def prefixEnd_5074944 : Nat := 4983230072969 + 3 ^ 40 * 5074944 * 2
def baseEnd_5074944 : Nat := 2605885566651097491960763

theorem tailTrace_5074944 : CollatzResearch.WordTrace tailWord_5074944 prefixEnd_5074944 2605885566651097491960763 := by
  unfold tailWord_5074944
  simp only [CollatzResearch.WordTrace]
  refine ⟨92549207063176047138147943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123398942750901396184197257 92549207063176047138147943)
  ·
    refine ⟨138823810594764070707221915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92549207063176047138147943 138823810594764070707221915)
    ·
      refine ⟨208235715892146106060832873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138823810594764070707221915 208235715892146106060832873)
      ·
        refine ⟨156176786919109579545624655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208235715892146106060832873 156176786919109579545624655)
        ·
          refine ⟨234265180378664369318436983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156176786919109579545624655 234265180378664369318436983)
          ·
            refine ⟨351397770567996553977655475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234265180378664369318436983 351397770567996553977655475)
            ·
              refine ⟨527096655851994830966483213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351397770567996553977655475 527096655851994830966483213)
              ·
                refine ⟨197661245944498061612431205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 527096655851994830966483213 197661245944498061612431205)
                ·
                  refine ⟨37061483614593386552330851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197661245944498061612431205 37061483614593386552330851)
                  ·
                    refine ⟨55592225421890079828496277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37061483614593386552330851 55592225421890079828496277)
                    ·
                      refine ⟨2605885566651097491960763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55592225421890079828496277 2605885566651097491960763)
                      ·
                        rfl

theorem cell23_5074944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_5074944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074944 prefixEnd_5074944 := by exact prefixLift 5074944
  have htrace : WordTrace (prefixWord ++ tailWord_5074944) baseStart_5074944 baseEnd_5074944 := by
    simpa [prefixWord, tailWord_5074944, baseEnd_5074944] using wordTrace_append hprefix tailTrace_5074944
  have hstable : (prefixWord ++ tailWord_5074944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074944).length < 2 ^ (prefixWord ++ tailWord_5074944).sum := by decide
  have hdescent : baseEnd_5074944 < baseStart_5074944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074958 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_5074958 : Nat := 118140960795 + 5074958 * 2 ^ 59
def prefixEnd_5074958 : Nat := 4983230072969 + 3 ^ 40 * 5074958 * 2
def baseEnd_5074958 : Nat := 868630918460086812395233

theorem tailTrace_5074958 : CollatzResearch.WordTrace tailWord_5074958 prefixEnd_5074958 868630918460086812395233 := by
  unfold tailWord_5074958
  simp only [CollatzResearch.WordTrace]
  refine ⟨23137365593537671833413191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123399283165534249778203685 23137365593537671833413191)
  ·
    refine ⟨34706048390306507750119787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23137365593537671833413191 34706048390306507750119787)
    ·
      refine ⟨52059072585459761625179681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34706048390306507750119787 52059072585459761625179681)
      ·
        refine ⟨39044304439094821218884761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52059072585459761625179681 39044304439094821218884761)
        ·
          refine ⟨29283228329321115914163571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39044304439094821218884761 29283228329321115914163571)
          ·
            refine ⟨43924842493981673871245357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29283228329321115914163571 43924842493981673871245357)
            ·
              refine ⟨16471815935243127701717009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43924842493981673871245357 16471815935243127701717009)
              ·
                refine ⟨12353861951432345776287757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16471815935243127701717009 12353861951432345776287757)
                ·
                  refine ⟨4632698231787129666107909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12353861951432345776287757 4632698231787129666107909)
                  ·
                    refine ⟨868630918460086812395233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632698231787129666107909 868630918460086812395233)
                    ·
                      rfl

theorem cell23_5074958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_5074958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074958 prefixEnd_5074958 := by exact prefixLift 5074958
  have htrace : WordTrace (prefixWord ++ tailWord_5074958) baseStart_5074958 baseEnd_5074958 := by
    simpa [prefixWord, tailWord_5074958, baseEnd_5074958] using wordTrace_append hprefix tailTrace_5074958
  have hstable : (prefixWord ++ tailWord_5074958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074958).length < 2 ^ (prefixWord ++ tailWord_5074958).sum := by decide
  have hdescent : baseEnd_5074958 < baseStart_5074958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074965 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_5074965 : Nat := 118140960795 + 5074965 * 2 ^ 59
def prefixEnd_5074965 : Nat := 4983230072969 + 3 ^ 40 * 5074965 * 2
def baseEnd_5074965 : Nat := 2605896349744841909798167

theorem tailTrace_5074965 : CollatzResearch.WordTrace tailWord_5074965 prefixEnd_5074965 2605896349744841909798167 := by
  unfold tailWord_5074965
  simp only [CollatzResearch.WordTrace]
  refine ⟨185099180059276014862810349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123399453372850676575206899 185099180059276014862810349)
  ·
    refine ⟨69412192522228505573553881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185099180059276014862810349 69412192522228505573553881)
    ·
      refine ⟨52059144391671379180165411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69412192522228505573553881 52059144391671379180165411)
      ·
        refine ⟨78088716587507068770248117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52059144391671379180165411 78088716587507068770248117)
        ·
          refine ⟨7320817180078787697210761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78088716587507068770248117 7320817180078787697210761)
          ·
            refine ⟨5490612885059090772908071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7320817180078787697210761 5490612885059090772908071)
            ·
              refine ⟨8235919327588636159362107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5490612885059090772908071 8235919327588636159362107)
              ·
                refine ⟨12353878991382954239043161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8235919327588636159362107 12353878991382954239043161)
                ·
                  refine ⟨9265409243537215679282371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12353878991382954239043161 9265409243537215679282371)
                  ·
                    refine ⟨13898113865305823518923557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9265409243537215679282371 13898113865305823518923557)
                    ·
                      refine ⟨2605896349744841909798167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13898113865305823518923557 2605896349744841909798167)
                      ·
                        rfl

theorem cell23_5074965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_5074965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074965 prefixEnd_5074965 := by exact prefixLift 5074965
  have htrace : WordTrace (prefixWord ++ tailWord_5074965) baseStart_5074965 baseEnd_5074965 := by
    simpa [prefixWord, tailWord_5074965, baseEnd_5074965] using wordTrace_append hprefix tailTrace_5074965
  have hstable : (prefixWord ++ tailWord_5074965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074965).length < 2 ^ (prefixWord ++ tailWord_5074965).sum := by decide
  have hdescent : baseEnd_5074965 < baseStart_5074965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5074975 : List Nat := [1, 1, 2, 4, 1, 2, 4, 3, 1, 4]
def baseStart_5074975 : Nat := 118140960795 + 5074975 * 2 ^ 59
def prefixEnd_5074975 : Nat := 4983230072969 + 3 ^ 40 * 5074975 * 2
def baseEnd_5074975 : Nat := 868633828183795623557707

theorem tailTrace_5074975 : CollatzResearch.WordTrace tailWord_5074975 prefixEnd_5074975 868633828183795623557707 := by
  unfold tailWord_5074975
  simp only [CollatzResearch.WordTrace]
  refine ⟨185099544789239786570674379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123399696526159857713782919 185099544789239786570674379)
  ·
    refine ⟨277649317183859679856011569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185099544789239786570674379 277649317183859679856011569)
    ·
      refine ⟨208236987887894759892008677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277649317183859679856011569 208236987887894759892008677)
      ·
        refine ⟨39044435228980267479751627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208236987887894759892008677 39044435228980267479751627)
        ·
          refine ⟨58566652843470401219627441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39044435228980267479751627 58566652843470401219627441)
          ·
            refine ⟨43924989632602800914720581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58566652843470401219627441 43924989632602800914720581)
            ·
              refine ⟨8235935556113025171510109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43924989632602800914720581 8235935556113025171510109)
              ·
                refine ⟨3088475833542384439316291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8235935556113025171510109 3088475833542384439316291)
                ·
                  refine ⟨4632713750313576658974437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088475833542384439316291 4632713750313576658974437)
                  ·
                    refine ⟨868633828183795623557707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632713750313576658974437 868633828183795623557707)
                    ·
                      rfl

theorem cell23_5074975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 4].length) (baseStart_5074975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5074975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5074975 prefixEnd_5074975 := by exact prefixLift 5074975
  have htrace : WordTrace (prefixWord ++ tailWord_5074975) baseStart_5074975 baseEnd_5074975 := by
    simpa [prefixWord, tailWord_5074975, baseEnd_5074975] using wordTrace_append hprefix tailTrace_5074975
  have hstable : (prefixWord ++ tailWord_5074975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5074975).length < 2 ^ (prefixWord ++ tailWord_5074975).sum := by decide
  have hdescent : baseEnd_5074975 < baseStart_5074975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5074975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075008 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 1, 5, 2]
def baseStart_5075008 : Nat := 118140960795 + 5075008 * 2 ^ 59
def prefixEnd_5075008 : Nat := 4983230072969 + 3 ^ 40 * 5075008 * 2
def baseEnd_5075008 : Nat := 2605918429412985241560469

theorem tailTrace_5075008 : CollatzResearch.WordTrace tailWord_5075008 prefixEnd_5075008 2605918429412985241560469 := by
  unfold tailWord_5075008
  simp only [CollatzResearch.WordTrace]
  refine ⟨92550374199060116603312839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123400498932080155471083785 92550374199060116603312839)
  ·
    refine ⟨138825561298590174904969259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92550374199060116603312839 138825561298590174904969259)
    ·
      refine ⟨208238341947885262357453889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138825561298590174904969259 208238341947885262357453889)
      ·
        refine ⟨156178756460913946768090417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208238341947885262357453889 156178756460913946768090417)
        ·
          refine ⟨117134067345685460076067813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156178756460913946768090417 117134067345685460076067813)
          ·
            refine ⟨21962637627316023764262715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117134067345685460076067813 21962637627316023764262715)
            ·
              refine ⟨32943956440974035646394073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21962637627316023764262715 32943956440974035646394073)
              ·
                refine ⟨24707967330730526734795555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32943956440974035646394073 24707967330730526734795555)
                ·
                  refine ⟨37061950996095790102193333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24707967330730526734795555 37061950996095790102193333)
                  ·
                    refine ⟨3474557905883980322080625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37061950996095790102193333 3474557905883980322080625)
                    ·
                      refine ⟨2605918429412985241560469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474557905883980322080625 2605918429412985241560469)
                      ·
                        rfl

theorem cell23_5075008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_5075008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075008 prefixEnd_5075008 := by exact prefixLift 5075008
  have htrace : WordTrace (prefixWord ++ tailWord_5075008) baseStart_5075008 baseEnd_5075008 := by
    simpa [prefixWord, tailWord_5075008, baseEnd_5075008] using wordTrace_append hprefix tailTrace_5075008
  have hstable : (prefixWord ++ tailWord_5075008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075008).length < 2 ^ (prefixWord ++ tailWord_5075008).sum := by decide
  have hdescent : baseEnd_5075008 < baseStart_5075008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075031 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 1, 6]
def baseStart_5075031 : Nat := 118140960795 + 5075031 * 2 ^ 59
def prefixEnd_5075031 : Nat := 4983230072969 + 3 ^ 40 * 5075031 * 2
def baseEnd_5075031 : Nat := 868643413156012883857621

theorem tailTrace_5075031 : CollatzResearch.WordTrace tailWord_5075031 prefixEnd_5075031 868643413156012883857621 := by
  unfold tailWord_5075031
  simp only [CollatzResearch.WordTrace]
  refine ⟨185101587277036908134712947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123401058184691272089808631 185101587277036908134712947)
  ·
    refine ⟨277652380915555362202069421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185101587277036908134712947 277652380915555362202069421)
    ·
      refine ⟨104119642843333260825776033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277652380915555362202069421 104119642843333260825776033)
      ·
        refine ⟨78089732132499945619332025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104119642843333260825776033 78089732132499945619332025)
        ·
          refine ⟨58567299099374959214499019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78089732132499945619332025 58567299099374959214499019)
          ·
            refine ⟨87850948649062438821748529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58567299099374959214499019 87850948649062438821748529)
            ·
              refine ⟨65888211486796829116311397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87850948649062438821748529 65888211486796829116311397)
              ·
                refine ⟨12354039653774405459308387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65888211486796829116311397 12354039653774405459308387)
                ·
                  refine ⟨18531059480661608188962581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12354039653774405459308387 18531059480661608188962581)
                  ·
                    refine ⟨868643413156012883857621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18531059480661608188962581 868643413156012883857621)
                    ·
                      rfl

theorem cell23_5075031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_5075031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075031 prefixEnd_5075031 := by exact prefixLift 5075031
  have htrace : WordTrace (prefixWord ++ tailWord_5075031) baseStart_5075031 baseEnd_5075031 := by
    simpa [prefixWord, tailWord_5075031, baseEnd_5075031] using wordTrace_append hprefix tailTrace_5075031
  have hstable : (prefixWord ++ tailWord_5075031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075031).length < 2 ^ (prefixWord ++ tailWord_5075031).sum := by decide
  have hdescent : baseEnd_5075031 < baseStart_5075031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075032 : List Nat := [2, 1, 2, 2, 1, 4, 3, 3, 1, 1, 3]
def baseStart_5075032 : Nat := 118140960795 + 5075032 * 2 ^ 59
def prefixEnd_5075032 : Nat := 4983230072969 + 3 ^ 40 * 5075032 * 2
def baseEnd_5075032 : Nat := 2605930752948693147660359

theorem tailTrace_5075032 : CollatzResearch.WordTrace tailWord_5075032 prefixEnd_5075032 2605930752948693147660359 := by
  unfold tailWord_5075032
  simp only [CollatzResearch.WordTrace]
  refine ⟨92550811875016642652749675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123401082500022190203666233 92550811875016642652749675)
  ·
    refine ⟨138826217812524963979124513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92550811875016642652749675 138826217812524963979124513)
    ·
      refine ⟨104119663359393722984343385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138826217812524963979124513 104119663359393722984343385)
      ·
        refine ⟨78089747519545292238257539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104119663359393722984343385 78089747519545292238257539)
        ·
          refine ⟨117134621279317938357386309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78089747519545292238257539 117134621279317938357386309)
          ·
            refine ⟨21962741489872113442009933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117134621279317938357386309 21962741489872113442009933)
            ·
              refine ⟨8236028058702042540753725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21962741489872113442009933 8236028058702042540753725)
              ·
                refine ⟨3088510522013265952782647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8236028058702042540753725 3088510522013265952782647)
                ·
                  refine ⟨4632765783019898929173971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088510522013265952782647 4632765783019898929173971)
                  ·
                    refine ⟨6949148674529848393760957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4632765783019898929173971 6949148674529848393760957)
                    ·
                      refine ⟨2605930752948693147660359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6949148674529848393760957 2605930752948693147660359)
                      ·
                        rfl

theorem cell23_5075032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_5075032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075032 prefixEnd_5075032 := by exact prefixLift 5075032
  have htrace : WordTrace (prefixWord ++ tailWord_5075032) baseStart_5075032 baseEnd_5075032 := by
    simpa [prefixWord, tailWord_5075032, baseEnd_5075032] using wordTrace_append hprefix tailTrace_5075032
  have hstable : (prefixWord ++ tailWord_5075032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075032).length < 2 ^ (prefixWord ++ tailWord_5075032).sum := by decide
  have hdescent : baseEnd_5075032 < baseStart_5075032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075058 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5075058 : Nat := 118140960795 + 5075058 * 2 ^ 59
def prefixEnd_5075058 : Nat := 4983230072969 + 3 ^ 40 * 5075058 * 2
def baseEnd_5075058 : Nat := 2605944103445710045935239

theorem tailTrace_5075058 : CollatzResearch.WordTrace tailWord_5075058 prefixEnd_5075058 2605944103445710045935239 := by
  unfold tailWord_5075058
  simp only [CollatzResearch.WordTrace]
  refine ⟨46275643011984772936486457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123401714698626061163963885 46275643011984772936486457)
  ·
    refine ⟨34706732258988579702364843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46275643011984772936486457 34706732258988579702364843)
    ·
      refine ⟨52060098388482869553547265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34706732258988579702364843 52060098388482869553547265)
      ·
        refine ⟨39045073791362152165160449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52060098388482869553547265 39045073791362152165160449)
        ·
          refine ⟨29283805343521614123870337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39045073791362152165160449 29283805343521614123870337)
          ·
            refine ⟨21962854007641210592902753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29283805343521614123870337 21962854007641210592902753)
            ·
              refine ⟨16472140505730907944677065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21962854007641210592902753 16472140505730907944677065)
              ·
                refine ⟨12354105379298180958507799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16472140505730907944677065 12354105379298180958507799)
                ·
                  refine ⟨18531158068947271437761699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12354105379298180958507799 18531158068947271437761699)
                  ·
                    refine ⟨27796737103420907156642549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18531158068947271437761699 27796737103420907156642549)
                    ·
                      refine ⟨2605944103445710045935239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27796737103420907156642549 2605944103445710045935239)
                      ·
                        rfl

theorem cell23_5075058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5075058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075058 prefixEnd_5075058 := by exact prefixLift 5075058
  have htrace : WordTrace (prefixWord ++ tailWord_5075058) baseStart_5075058 baseEnd_5075058 := by
    simpa [prefixWord, tailWord_5075058, baseEnd_5075058] using wordTrace_append hprefix tailTrace_5075058
  have hstable : (prefixWord ++ tailWord_5075058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075058).length < 2 ^ (prefixWord ++ tailWord_5075058).sum := by decide
  have hdescent : baseEnd_5075058 < baseStart_5075058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075065 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 2, 4]
def baseStart_5075065 : Nat := 118140960795 + 5075065 * 2 ^ 59
def prefixEnd_5075065 : Nat := 4983230072969 + 3 ^ 40 * 5075065 * 2
def baseEnd_5075065 : Nat := 868649232603430506182569

theorem tailTrace_5075065 : CollatzResearch.WordTrace tailWord_5075065 prefixEnd_5075065 868649232603430506182569 := by
  unfold tailWord_5075065
  simp only [CollatzResearch.WordTrace]
  refine ⟨185102827358913731941450649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123401884905942487960967099 185102827358913731941450649)
  ·
    refine ⟨138827120519185298956087987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185102827358913731941450649 138827120519185298956087987)
    ·
      refine ⟨208240680778777948434131981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138827120519185298956087987 208240680778777948434131981)
      ·
        refine ⟨78090255292041730662799493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208240680778777948434131981 78090255292041730662799493)
        ·
          refine ⟨14641922867257824499274905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78090255292041730662799493 14641922867257824499274905)
          ·
            refine ⟨10981442150443368374456179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14641922867257824499274905 10981442150443368374456179)
            ·
              refine ⟨16472163225665052561684269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10981442150443368374456179 16472163225665052561684269)
              ·
                refine ⟨6177061209624394710631601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16472163225665052561684269 6177061209624394710631601)
                ·
                  refine ⟨4632795907218296032973701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177061209624394710631601 4632795907218296032973701)
                  ·
                    refine ⟨868649232603430506182569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632795907218296032973701 868649232603430506182569)
                    ·
                      rfl

theorem cell23_5075065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_5075065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075065 prefixEnd_5075065 := by exact prefixLift 5075065
  have htrace : WordTrace (prefixWord ++ tailWord_5075065) baseStart_5075065 baseEnd_5075065 := by
    simpa [prefixWord, tailWord_5075065, baseEnd_5075065] using wordTrace_append hprefix tailTrace_5075065
  have hstable : (prefixWord ++ tailWord_5075065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075065).length < 2 ^ (prefixWord ++ tailWord_5075065).sum := by decide
  have hdescent : baseEnd_5075065 < baseStart_5075065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075075 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 3]
def baseStart_5075075 : Nat := 118140960795 + 5075075 * 2 ^ 59
def prefixEnd_5075075 : Nat := 4983230072969 + 3 ^ 40 * 5075075 * 2
def baseEnd_5075075 : Nat := 2605952832616836479422661

theorem tailTrace_5075075 : CollatzResearch.WordTrace tailWord_5075075 prefixEnd_5075075 2605952832616836479422661 := by
  unfold tailWord_5075075
  simp only [CollatzResearch.WordTrace]
  refine ⟨185103192088877503649314679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123402128059251669099543119 185103192088877503649314679)
  ·
    refine ⟨277654788133316255473972019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185103192088877503649314679 277654788133316255473972019)
    ·
      refine ⟨416482182199974383210958029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277654788133316255473972019 416482182199974383210958029)
      ·
        refine ⟨156180818324990393704109261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416482182199974383210958029 156180818324990393704109261)
        ·
          refine ⟨58567806871871397639040973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156180818324990393704109261 58567806871871397639040973)
          ·
            refine ⟨21962927576951774114640365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58567806871871397639040973 21962927576951774114640365)
            ·
              refine ⟨8236097841356915292990137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21962927576951774114640365 8236097841356915292990137)
              ·
                refine ⟨6177073381017686469742603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8236097841356915292990137 6177073381017686469742603)
                ·
                  refine ⟨9265610071526529704613905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6177073381017686469742603 9265610071526529704613905)
                  ·
                    refine ⟨6949207553644897278460429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9265610071526529704613905 6949207553644897278460429)
                    ·
                      refine ⟨2605952832616836479422661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6949207553644897278460429 2605952832616836479422661)
                      ·
                        rfl

theorem cell23_5075075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_5075075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075075 prefixEnd_5075075 := by exact prefixLift 5075075
  have htrace : WordTrace (prefixWord ++ tailWord_5075075) baseStart_5075075 baseEnd_5075075 := by
    simpa [prefixWord, tailWord_5075075, baseEnd_5075075] using wordTrace_append hprefix tailTrace_5075075
  have hstable : (prefixWord ++ tailWord_5075075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075075).length < 2 ^ (prefixWord ++ tailWord_5075075).sum := by decide
  have hdescent : baseEnd_5075075 < baseStart_5075075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075088 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3]
def baseStart_5075088 : Nat := 118140960795 + 5075088 * 2 ^ 59
def prefixEnd_5075088 : Nat := 4983230072969 + 3 ^ 40 * 5075088 * 2
def baseEnd_5075088 : Nat := 2605959507865344928560101

theorem tailTrace_5075088 : CollatzResearch.WordTrace tailWord_5075088 prefixEnd_5075088 2605959507865344928560101 := by
  unfold tailWord_5075088
  simp only [CollatzResearch.WordTrace]
  refine ⟨92551833118915203434768959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123402444158553604579691945 92551833118915203434768959)
  ·
    refine ⟨138827749678372805152153439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92551833118915203434768959 138827749678372805152153439)
    ·
      refine ⟨208241624517559207728230159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138827749678372805152153439 208241624517559207728230159)
      ·
        refine ⟨312362436776338811592345239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208241624517559207728230159 312362436776338811592345239)
        ·
          refine ⟨468543655164508217388517859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312362436776338811592345239 468543655164508217388517859)
          ·
            refine ⟨702815482746762326082776789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468543655164508217388517859 702815482746762326082776789)
            ·
              refine ⟨16472237876877242017565081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 702815482746762326082776789 16472237876877242017565081)
              ·
                refine ⟨12354178407657931513173811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16472237876877242017565081 12354178407657931513173811)
                ·
                  refine ⟨18531267611486897269760717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12354178407657931513173811 18531267611486897269760717)
                  ·
                    refine ⟨6949225354307586476160269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18531267611486897269760717 6949225354307586476160269)
                    ·
                      refine ⟨2605959507865344928560101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6949225354307586476160269 2605959507865344928560101)
                      ·
                        rfl

theorem cell23_5075088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_5075088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075088 prefixEnd_5075088 := by exact prefixLift 5075088
  have htrace : WordTrace (prefixWord ++ tailWord_5075088) baseStart_5075088 baseEnd_5075088 := by
    simpa [prefixWord, tailWord_5075088, baseEnd_5075088] using wordTrace_append hprefix tailTrace_5075088
  have hstable : (prefixWord ++ tailWord_5075088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075088).length < 2 ^ (prefixWord ++ tailWord_5075088).sum := by decide
  have hdescent : baseEnd_5075088 < baseStart_5075088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075106 : List Nat := [3, 3, 1, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_5075106 : Nat := 118140960795 + 5075106 * 2 ^ 59
def prefixEnd_5075106 : Nat := 4983230072969 + 3 ^ 40 * 5075106 * 2
def baseEnd_5075106 : Nat := 2605968750517125858135019

theorem tailTrace_5075106 : CollatzResearch.WordTrace tailWord_5075106 prefixEnd_5075106 2605968750517125858135019 := by
  unfold tailWord_5075106
  simp only [CollatzResearch.WordTrace]
  refine ⟨46276080687941298985923293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123402881834510130629128781 46276080687941298985923293)
  ·
    refine ⟨17353530257977987119721235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46276080687941298985923293 17353530257977987119721235)
    ·
      refine ⟨26030295386966980679581853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17353530257977987119721235 26030295386966980679581853)
      ·
        refine ⟨9761360770112617754843195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26030295386966980679581853 9761360770112617754843195)
        ·
          refine ⟨14642041155168926632264793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761360770112617754843195 14642041155168926632264793)
          ·
            refine ⟨10981530866376694974198595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14642041155168926632264793 10981530866376694974198595)
            ·
              refine ⟨16472296299565042461297893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10981530866376694974198595 16472296299565042461297893)
              ·
                refine ⟨3088555556168445461493355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16472296299565042461297893 3088555556168445461493355)
                ·
                  refine ⟨4632833334252668192240033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088555556168445461493355 4632833334252668192240033)
                  ·
                    refine ⟨3474625000689501144180025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4632833334252668192240033 3474625000689501144180025)
                    ·
                      refine ⟨2605968750517125858135019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474625000689501144180025 2605968750517125858135019)
                      ·
                        rfl

theorem cell23_5075106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_5075106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075106 prefixEnd_5075106 := by exact prefixLift 5075106
  have htrace : WordTrace (prefixWord ++ tailWord_5075106) baseStart_5075106 baseEnd_5075106 := by
    simpa [prefixWord, tailWord_5075106, baseEnd_5075106] using wordTrace_append hprefix tailTrace_5075106
  have hstable : (prefixWord ++ tailWord_5075106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075106).length < 2 ^ (prefixWord ++ tailWord_5075106).sum := by decide
  have hdescent : baseEnd_5075106 < baseStart_5075106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075151 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 9]
def baseStart_5075151 : Nat := 118140960795 + 5075151 * 2 ^ 59
def prefixEnd_5075151 : Nat := 4983230072969 + 3 ^ 40 * 5075151 * 2
def baseEnd_5075151 : Nat := 289554650794064242452479

theorem tailTrace_5075151 : CollatzResearch.WordTrace tailWord_5075151 prefixEnd_5075151 289554650794064242452479 := by
  unfold tailWord_5075151
  simp only [CollatzResearch.WordTrace]
  refine ⟨185105964036602168629081307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123403976024401445752720871 185105964036602168629081307)
  ·
    refine ⟨277658946054903252943621961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185105964036602168629081307 277658946054903252943621961)
    ·
      refine ⟨208244209541177439707716471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277658946054903252943621961 208244209541177439707716471)
      ·
        refine ⟨312366314311766159561574707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208244209541177439707716471 312366314311766159561574707)
        ·
          refine ⟨468549471467649239342362061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312366314311766159561574707 468549471467649239342362061)
          ·
            refine ⟨175706051800368464753385773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468549471467649239342362061 175706051800368464753385773)
            ·
              refine ⟨65889769425138174282519665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175706051800368464753385773 65889769425138174282519665)
              ·
                refine ⟨49417327068853630711889749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65889769425138174282519665 49417327068853630711889749)
                ·
                  refine ⟨289554650794064242452479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49417327068853630711889749 289554650794064242452479)
                  ·
                    rfl

theorem cell23_5075151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 9].length) (baseStart_5075151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075151 prefixEnd_5075151 := by exact prefixLift 5075151
  have htrace : WordTrace (prefixWord ++ tailWord_5075151) baseStart_5075151 baseEnd_5075151 := by
    simpa [prefixWord, tailWord_5075151, baseEnd_5075151] using wordTrace_append hprefix tailTrace_5075151
  have hstable : (prefixWord ++ tailWord_5075151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075151).length < 2 ^ (prefixWord ++ tailWord_5075151).sum := by decide
  have hdescent : baseEnd_5075151 < baseStart_5075151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075168 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 7]
def baseStart_5075168 : Nat := 118140960795 + 5075168 * 2 ^ 59
def prefixEnd_5075168 : Nat := 4983230072969 + 3 ^ 40 * 5075168 * 2
def baseEnd_5075168 : Nat := 289555620701967179506637

theorem tailTrace_5075168 : CollatzResearch.WordTrace tailWord_5075168 prefixEnd_5075168 289555620701967179506637 := by
  unfold tailWord_5075168
  simp only [CollatzResearch.WordTrace]
  refine ⟨92553292038770290266225079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123404389385027053688300105 92553292038770290266225079)
  ·
    refine ⟨138829938058155435399337619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92553292038770290266225079 138829938058155435399337619)
    ·
      refine ⟨208244907087233153099006429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138829938058155435399337619 208244907087233153099006429)
      ·
        refine ⟨78091840157712432412127411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208244907087233153099006429 78091840157712432412127411)
        ·
          refine ⟨117137760236568648618191117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78091840157712432412127411 117137760236568648618191117)
          ·
            refine ⟨43926660088713243231821669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117137760236568648618191117 43926660088713243231821669)
            ·
              refine ⟨8236248766633733105966563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43926660088713243231821669 8236248766633733105966563)
              ·
                refine ⟨12354373149950599658949845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8236248766633733105966563 12354373149950599658949845)
                ·
                  refine ⟨289555620701967179506637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12354373149950599658949845 289555620701967179506637)
                  ·
                    rfl

theorem cell23_5075168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 7].length) (baseStart_5075168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075168 prefixEnd_5075168 := by exact prefixLift 5075168
  have htrace : WordTrace (prefixWord ++ tailWord_5075168) baseStart_5075168 baseEnd_5075168 := by
    simpa [prefixWord, tailWord_5075168, baseEnd_5075168] using wordTrace_append hprefix tailTrace_5075168
  have hstable : (prefixWord ++ tailWord_5075168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075168).length < 2 ^ (prefixWord ++ tailWord_5075168).sum := by decide
  have hdescent : baseEnd_5075168 < baseStart_5075168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075175 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5075175 : Nat := 118140960795 + 5075175 * 2 ^ 59
def prefixEnd_5075175 : Nat := 4983230072969 + 3 ^ 40 * 5075175 * 2
def baseEnd_5075175 : Nat := 2606004180682286088172201

theorem tailTrace_5075175 : CollatzResearch.WordTrace tailWord_5075175 prefixEnd_5075175 2606004180682286088172201 := by
  unfold tailWord_5075175
  simp only [CollatzResearch.WordTrace]
  refine ⟨185106839388515220727954979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123404559592343480485303319 185106839388515220727954979)
  ·
    refine ⟨277660259082772831091932469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185106839388515220727954979 277660259082772831091932469)
    ·
      refine ⟨26030649289009952914868669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277660259082772831091932469 26030649289009952914868669)
      ·
        refine ⟨9761493483378732343075751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26030649289009952914868669 9761493483378732343075751)
        ·
          refine ⟨14642240225068098514613627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761493483378732343075751 14642240225068098514613627)
          ·
            refine ⟨21963360337602147771920441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14642240225068098514613627 21963360337602147771920441)
            ·
              refine ⟨16472520253201610828940331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21963360337602147771920441 16472520253201610828940331)
              ·
                refine ⟨24708780379802416243410497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16472520253201610828940331 24708780379802416243410497)
                ·
                  refine ⟨18531585284851812182557873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24708780379802416243410497 18531585284851812182557873)
                  ·
                    refine ⟨13898688963638859136918405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18531585284851812182557873 13898688963638859136918405)
                    ·
                      refine ⟨2606004180682286088172201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13898688963638859136918405 2606004180682286088172201)
                      ·
                        rfl

theorem cell23_5075175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5075175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075175 prefixEnd_5075175 := by exact prefixLift 5075175
  have htrace : WordTrace (prefixWord ++ tailWord_5075175) baseStart_5075175 baseEnd_5075175 := by
    simpa [prefixWord, tailWord_5075175, baseEnd_5075175] using wordTrace_append hprefix tailTrace_5075175
  have hstable : (prefixWord ++ tailWord_5075175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075175).length < 2 ^ (prefixWord ++ tailWord_5075175).sum := by decide
  have hdescent : baseEnd_5075175 < baseStart_5075175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075179 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 2, 2, 2]
def baseStart_5075179 : Nat := 118140960795 + 5075179 * 2 ^ 59
def prefixEnd_5075179 : Nat := 4983230072969 + 3 ^ 40 * 5075179 * 2
def baseEnd_5075179 : Nat := 2606006234604904072522183

theorem tailTrace_5075179 : CollatzResearch.WordTrace tailWord_5075179 prefixEnd_5075179 2606006234604904072522183 := by
  unfold tailWord_5075179
  simp only [CollatzResearch.WordTrace]
  refine ⟨185106985280500729411100591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123404656853667152940733727 185106985280500729411100591)
  ·
    refine ⟨277660477920751094116650887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185106985280500729411100591 277660477920751094116650887)
    ·
      refine ⟨416490716881126641174976331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277660477920751094116650887 416490716881126641174976331)
      ·
        refine ⟨624736075321689961762464497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416490716881126641174976331 624736075321689961762464497)
        ·
          refine ⟨468552056491267471321848373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624736075321689961762464497 468552056491267471321848373)
          ·
            refine ⟨43926755296056325436423285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 468552056491267471321848373 43926755296056325436423285)
            ·
              refine ⟨4118133309005280509664683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43926755296056325436423285 4118133309005280509664683)
              ·
                refine ⟨6177199963507920764497025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118133309005280509664683 6177199963507920764497025)
                ·
                  refine ⟨4632899972630940573372769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177199963507920764497025 4632899972630940573372769)
                  ·
                    refine ⟨3474674979473205430029577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4632899972630940573372769 3474674979473205430029577)
                    ·
                      refine ⟨2606006234604904072522183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474674979473205430029577 2606006234604904072522183)
                      ·
                        rfl

theorem cell23_5075179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 2, 2].length) (baseStart_5075179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075179 prefixEnd_5075179 := by exact prefixLift 5075179
  have htrace : WordTrace (prefixWord ++ tailWord_5075179) baseStart_5075179 baseEnd_5075179 := by
    simpa [prefixWord, tailWord_5075179, baseEnd_5075179] using wordTrace_append hprefix tailTrace_5075179
  have hstable : (prefixWord ++ tailWord_5075179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075179).length < 2 ^ (prefixWord ++ tailWord_5075179).sum := by decide
  have hdescent : baseEnd_5075179 < baseStart_5075179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075230 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5075230 : Nat := 118140960795 + 5075230 * 2 ^ 59
def prefixEnd_5075230 : Nat := 4983230072969 + 3 ^ 40 * 5075230 * 2
def baseEnd_5075230 : Nat := 2606032422118283372984449

theorem tailTrace_5075230 : CollatzResearch.WordTrace tailWord_5075230 prefixEnd_5075230 2606032422118283372984449 := by
  unfold tailWord_5075230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23138605675414495640150893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123405896935543976747471429 23138605675414495640150893)
  ·
    refine ⟨8676977128280435865056585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23138605675414495640150893 8676977128280435865056585)
    ·
      refine ⟨6507732846210326898792439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8676977128280435865056585 6507732846210326898792439)
      ·
        refine ⟨9761599269315490348188659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6507732846210326898792439 9761599269315490348188659)
        ·
          refine ⟨14642398903973235522282989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761599269315490348188659 14642398903973235522282989)
          ·
            refine ⟨5490899588989963320856121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14642398903973235522282989 5490899588989963320856121)
            ·
              refine ⟨4118174691742472490642091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490899588989963320856121 4118174691742472490642091)
              ·
                refine ⟨6177262037613708735963137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118174691742472490642091 6177262037613708735963137)
                ·
                  refine ⟨4632946528210281551972353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177262037613708735963137 4632946528210281551972353)
                  ·
                    refine ⟨3474709896157711163979265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4632946528210281551972353 3474709896157711163979265)
                    ·
                      refine ⟨2606032422118283372984449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474709896157711163979265 2606032422118283372984449)
                      ·
                        rfl

theorem cell23_5075230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5075230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075230 prefixEnd_5075230 := by exact prefixLift 5075230
  have htrace : WordTrace (prefixWord ++ tailWord_5075230) baseStart_5075230 baseEnd_5075230 := by
    simpa [prefixWord, tailWord_5075230, baseEnd_5075230] using wordTrace_append hprefix tailTrace_5075230
  have hstable : (prefixWord ++ tailWord_5075230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075230).length < 2 ^ (prefixWord ++ tailWord_5075230).sum := by decide
  have hdescent : baseEnd_5075230 < baseStart_5075230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075235 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 1, 6, 2]
def baseStart_5075235 : Nat := 118140960795 + 5075235 * 2 ^ 59
def prefixEnd_5075235 : Nat := 4983230072969 + 3 ^ 40 * 5075235 * 2
def baseEnd_5075235 : Nat := 2606034989521555853421925

theorem tailTrace_5075235 : CollatzResearch.WordTrace tailWord_5075235 prefixEnd_5075235 2606034989521555853421925 := by
  unfold tailWord_5075235
  simp only [CollatzResearch.WordTrace]
  refine ⟨185109027768297850975139159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123406018512198567316759439 185109027768297850975139159)
  ·
    refine ⟨277663541652446776462708739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185109027768297850975139159 277663541652446776462708739)
    ·
      refine ⟨416495312478670164694063109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277663541652446776462708739 416495312478670164694063109)
      ·
        refine ⟨78092871089750655880136833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 416495312478670164694063109 78092871089750655880136833)
        ·
          refine ⟨58569653317312991910102625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78092871089750655880136833 58569653317312991910102625)
          ·
            refine ⟨43927239987984743932576969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58569653317312991910102625 43927239987984743932576969)
            ·
              refine ⟨32945429990988557949432727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43927239987984743932576969 32945429990988557949432727)
              ·
                refine ⟨49418144986482836924149091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32945429990988557949432727 49418144986482836924149091)
                ·
                  refine ⟨74127217479724255386223637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49418144986482836924149091 74127217479724255386223637)
                  ·
                    refine ⟨3474713319362074471229233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74127217479724255386223637 3474713319362074471229233)
                    ·
                      refine ⟨2606034989521555853421925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474713319362074471229233 2606034989521555853421925)
                      ·
                        rfl

theorem cell23_5075235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_5075235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075235 prefixEnd_5075235 := by exact prefixLift 5075235
  have htrace : WordTrace (prefixWord ++ tailWord_5075235) baseStart_5075235 baseEnd_5075235 := by
    simpa [prefixWord, tailWord_5075235, baseEnd_5075235] using wordTrace_append hprefix tailTrace_5075235
  have hstable : (prefixWord ++ tailWord_5075235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075235).length < 2 ^ (prefixWord ++ tailWord_5075235).sum := by decide
  have hdescent : baseEnd_5075235 < baseStart_5075235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075252 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5075252 : Nat := 118140960795 + 5075252 * 2 ^ 59
def prefixEnd_5075252 : Nat := 4983230072969 + 3 ^ 40 * 5075252 * 2
def baseEnd_5075252 : Nat := 2606043718692682286909347

theorem tailTrace_5075252 : CollatzResearch.WordTrace tailWord_5075252 prefixEnd_5075252 2606043718692682286909347 := by
  unfold tailWord_5075252
  simp only [CollatzResearch.WordTrace]
  refine ⟨92554823904618131439254005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123406431872824175252338673 92554823904618131439254005)
  ·
    refine ⟨8677014741057949822430063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92554823904618131439254005 8677014741057949822430063)
    ·
      refine ⟨13015522111586924733645095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8677014741057949822430063 13015522111586924733645095)
      ·
        refine ⟨19523283167380387100467643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13015522111586924733645095 19523283167380387100467643)
        ·
          refine ⟨29284924751070580650701465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19523283167380387100467643 29284924751070580650701465)
          ·
            refine ⟨21963693563302935488026099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29284924751070580650701465 21963693563302935488026099)
            ·
              refine ⟨32945540344954403232039149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21963693563302935488026099 32945540344954403232039149)
              ·
                refine ⟨12354577629357901212014681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32945540344954403232039149 12354577629357901212014681)
                ·
                  refine ⟨9265933222018425909011011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12354577629357901212014681 9265933222018425909011011)
                  ·
                    refine ⟨13898899833027638863516517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9265933222018425909011011 13898899833027638863516517)
                    ·
                      refine ⟨2606043718692682286909347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13898899833027638863516517 2606043718692682286909347)
                      ·
                        rfl

theorem cell23_5075252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5075252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075252 prefixEnd_5075252 := by exact prefixLift 5075252
  have htrace : WordTrace (prefixWord ++ tailWord_5075252) baseStart_5075252 baseEnd_5075252 := by
    simpa [prefixWord, tailWord_5075252, baseEnd_5075252] using wordTrace_append hprefix tailTrace_5075252
  have hstable : (prefixWord ++ tailWord_5075252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075252).length < 2 ^ (prefixWord ++ tailWord_5075252).sum := by decide
  have hdescent : baseEnd_5075252 < baseStart_5075252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075305 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 1, 5]
def baseStart_5075305 : Nat := 118140960795 + 5075305 * 2 ^ 59
def prefixEnd_5075305 : Nat := 4983230072969 + 3 ^ 40 * 5075305 * 2
def baseEnd_5075305 : Nat := 868690311055790193182201

theorem tailTrace_5075305 : CollatzResearch.WordTrace tailWord_5075305 prefixEnd_5075305 868690311055790193182201 := by
  unfold tailWord_5075305
  simp only [CollatzResearch.WordTrace]
  refine ⟨185111580878044252930187369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123407720585362835286791579 185111580878044252930187369)
  ·
    refine ⟨138833685658533189697640527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185111580878044252930187369 138833685658533189697640527)
    ·
      refine ⟨208250528487799784546460791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138833685658533189697640527 208250528487799784546460791)
      ·
        refine ⟨312375792731699676819691187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208250528487799784546460791 312375792731699676819691187)
        ·
          refine ⟨468563689097549515229536781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312375792731699676819691187 468563689097549515229536781)
          ·
            refine ⟨175711383411581068211076293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468563689097549515229536781 175711383411581068211076293)
            ·
              refine ⟨32945884389671450289576805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175711383411581068211076293 32945884389671450289576805)
              ·
                refine ⟨6177353323063396929295651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32945884389671450289576805 6177353323063396929295651)
                ·
                  refine ⟨9266029984595095393943477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6177353323063396929295651 9266029984595095393943477)
                  ·
                    refine ⟨868690311055790193182201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9266029984595095393943477 868690311055790193182201)
                    ·
                      rfl

theorem cell23_5075305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_5075305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075305 prefixEnd_5075305 := by exact prefixLift 5075305
  have htrace : WordTrace (prefixWord ++ tailWord_5075305) baseStart_5075305 baseEnd_5075305 := by
    simpa [prefixWord, tailWord_5075305, baseEnd_5075305] using wordTrace_append hprefix tailTrace_5075305
  have hstable : (prefixWord ++ tailWord_5075305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075305).length < 2 ^ (prefixWord ++ tailWord_5075305).sum := by decide
  have hdescent : baseEnd_5075305 < baseStart_5075305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075312 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 1, 5, 2]
def baseStart_5075312 : Nat := 118140960795 + 5075312 * 2 ^ 59
def prefixEnd_5075312 : Nat := 4983230072969 + 3 ^ 40 * 5075312 * 2
def baseEnd_5075312 : Nat := 2606074527531952052159071

theorem tailTrace_5075312 : CollatzResearch.WordTrace tailWord_5075312 prefixEnd_5075312 2606074527531952052159071 := by
  unfold tailWord_5075312
  simp only [CollatzResearch.WordTrace]
  refine ⟨92555918094509446562846095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123407890792679262083794793 92555918094509446562846095)
  ·
    refine ⟨138833877141764169844269143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92555918094509446562846095 138833877141764169844269143)
    ·
      refine ⟨208250815712646254766403715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138833877141764169844269143 208250815712646254766403715)
      ·
        refine ⟨312376223568969382149605573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208250815712646254766403715 312376223568969382149605573)
        ·
          refine ⟨58570541919181759153051045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312376223568969382149605573 58570541919181759153051045)
          ·
            refine ⟨10981976609846579841197071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58570541919181759153051045 10981976609846579841197071)
            ·
              refine ⟨16472964914769869761795607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10981976609846579841197071 16472964914769869761795607)
              ·
                refine ⟨24709447372154804642693411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16472964914769869761795607 24709447372154804642693411)
                ·
                  refine ⟨37064171058232206964040117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24709447372154804642693411 37064171058232206964040117)
                  ·
                    refine ⟨3474766036709269402878761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37064171058232206964040117 3474766036709269402878761)
                    ·
                      refine ⟨2606074527531952052159071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474766036709269402878761 2606074527531952052159071)
                      ·
                        rfl

theorem cell23_5075312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 5, 2].length) (baseStart_5075312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075312 prefixEnd_5075312 := by exact prefixLift 5075312
  have htrace : WordTrace (prefixWord ++ tailWord_5075312) baseStart_5075312 baseEnd_5075312 := by
    simpa [prefixWord, tailWord_5075312, baseEnd_5075312] using wordTrace_append hprefix tailTrace_5075312
  have hstable : (prefixWord ++ tailWord_5075312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075312).length < 2 ^ (prefixWord ++ tailWord_5075312).sum := by decide
  have hdescent : baseEnd_5075312 < baseStart_5075312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075352 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 1, 6]
def baseStart_5075352 : Nat := 118140960795 + 5075352 * 2 ^ 59
def prefixEnd_5075352 : Nat := 4983230072969 + 3 ^ 40 * 5075352 * 2
def baseEnd_5075352 : Nat := 868698355586043965219629

theorem tailTrace_5075352 : CollatzResearch.WordTrace tailWord_5075352 prefixEnd_5075352 868698355586043965219629 := by
  unfold tailWord_5075352
  simp only [CollatzResearch.WordTrace]
  refine ⟨92556647554436989978574155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123408863405915986638098873 92556647554436989978574155)
  ·
    refine ⟨138834971331655484967861233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92556647554436989978574155 138834971331655484967861233)
    ·
      refine ⟨104126228498741613725895925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138834971331655484967861233 104126228498741613725895925)
      ·
        refine ⟨9761833921757026286802743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104126228498741613725895925 9761833921757026286802743)
        ·
          refine ⟨14642750882635539430204115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761833921757026286802743 14642750882635539430204115)
          ·
            refine ⟨21964126323953309145306173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14642750882635539430204115 21964126323953309145306173)
            ·
              refine ⟨8236547371482490929489815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21964126323953309145306173 8236547371482490929489815)
              ·
                refine ⟨12354821057223736394234723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8236547371482490929489815 12354821057223736394234723)
                ·
                  refine ⟨18532231585835604591352085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12354821057223736394234723 18532231585835604591352085)
                  ·
                    refine ⟨868698355586043965219629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18532231585835604591352085 868698355586043965219629)
                    ·
                      rfl

theorem cell23_5075352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_5075352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075352 prefixEnd_5075352 := by exact prefixLift 5075352
  have htrace : WordTrace (prefixWord ++ tailWord_5075352) baseStart_5075352 baseEnd_5075352 := by
    simpa [prefixWord, tailWord_5075352, baseEnd_5075352] using wordTrace_append hprefix tailTrace_5075352
  have hstable : (prefixWord ++ tailWord_5075352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075352).length < 2 ^ (prefixWord ++ tailWord_5075352).sum := by decide
  have hdescent : baseEnd_5075352 < baseStart_5075352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075359 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 3, 2, 2]
def baseStart_5075359 : Nat := 118140960795 + 5075359 * 2 ^ 59
def prefixEnd_5075359 : Nat := 4983230072969 + 3 ^ 40 * 5075359 * 2
def baseEnd_5075359 : Nat := 2606098661122713368271355

theorem tailTrace_5075359 : CollatzResearch.WordTrace tailWord_5075359 prefixEnd_5075359 2606098661122713368271355 := by
  unfold tailWord_5075359
  simp only [CollatzResearch.WordTrace]
  refine ⟨185113550419848620152653131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123409033613232413435102087 185113550419848620152653131)
  ·
    refine ⟨277670325629772930228979697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185113550419848620152653131 277670325629772930228979697)
    ·
      refine ⟨208252744222329697671734773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277670325629772930228979697 208252744222329697671734773)
      ·
        refine ⟨19523694770843409156725135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208252744222329697671734773 19523694770843409156725135)
        ·
          refine ⟨29285542156265113735087703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19523694770843409156725135 29285542156265113735087703)
          ·
            refine ⟨43928313234397670602631555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29285542156265113735087703 43928313234397670602631555)
            ·
              refine ⟨65892469851596505903947333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43928313234397670602631555 65892469851596505903947333)
              ·
                refine ⟨12354838097174344856990125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65892469851596505903947333 12354838097174344856990125)
                ·
                  refine ⟨4633064286440379321371297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12354838097174344856990125 4633064286440379321371297)
                  ·
                    refine ⟨3474798214830284491028473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633064286440379321371297 3474798214830284491028473)
                    ·
                      refine ⟨2606098661122713368271355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474798214830284491028473 2606098661122713368271355)
                      ·
                        rfl

theorem cell23_5075359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_5075359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075359 prefixEnd_5075359 := by exact prefixLift 5075359
  have htrace : WordTrace (prefixWord ++ tailWord_5075359) baseStart_5075359 baseEnd_5075359 := by
    simpa [prefixWord, tailWord_5075359, baseEnd_5075359] using wordTrace_append hprefix tailTrace_5075359
  have hstable : (prefixWord ++ tailWord_5075359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075359).length < 2 ^ (prefixWord ++ tailWord_5075359).sum := by decide
  have hdescent : baseEnd_5075359 < baseStart_5075359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075435 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5]
def baseStart_5075435 : Nat := 118140960795 + 5075435 * 2 ^ 59
def prefixEnd_5075435 : Nat := 4983230072969 + 3 ^ 40 * 5075435 * 2
def baseEnd_5075435 : Nat := 2606137685652455070921005

theorem tailTrace_5075435 : CollatzResearch.WordTrace tailWord_5075435 prefixEnd_5075435 2606137685652455070921005 := by
  unfold tailWord_5075435
  simp only [CollatzResearch.WordTrace]
  refine ⟨185116322367573285132419759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123410881578382190088279839 185116322367573285132419759)
  ·
    refine ⟨277674483551359927698629639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185116322367573285132419759 277674483551359927698629639)
    ·
      refine ⟨416511725327039891547944459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277674483551359927698629639 416511725327039891547944459)
      ·
        refine ⟨624767587990559837321916689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416511725327039891547944459 624767587990559837321916689)
        ·
          refine ⟨468575690992919877991437517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624767587990559837321916689 468575690992919877991437517)
          ·
            refine ⟨175715884122344954246789069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468575690992919877991437517 175715884122344954246789069)
            ·
              refine ⟨65893456545879357842545901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175715884122344954246789069 65893456545879357842545901)
              ·
                refine ⟨24710046204704759190954713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65893456545879357842545901 24710046204704759190954713)
                ·
                  refine ⟨18532534653528569393216035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24710046204704759190954713 18532534653528569393216035)
                  ·
                    refine ⟨27798801980292854089824053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18532534653528569393216035 27798801980292854089824053)
                    ·
                      refine ⟨2606137685652455070921005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27798801980292854089824053 2606137685652455070921005)
                      ·
                        rfl

theorem cell23_5075435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_5075435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075435 prefixEnd_5075435 := by exact prefixLift 5075435
  have htrace : WordTrace (prefixWord ++ tailWord_5075435) baseStart_5075435 baseEnd_5075435 := by
    simpa [prefixWord, tailWord_5075435, baseEnd_5075435] using wordTrace_append hprefix tailTrace_5075435
  have hstable : (prefixWord ++ tailWord_5075435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075435).length < 2 ^ (prefixWord ++ tailWord_5075435).sum := by decide
  have hdescent : baseEnd_5075435 < baseStart_5075435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075436 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 1, 3, 2]
def baseStart_5075436 : Nat := 118140960795 + 5075436 * 2 ^ 59
def prefixEnd_5075436 : Nat := 4983230072969 + 3 ^ 40 * 5075436 * 2
def baseEnd_5075436 : Nat := 2606138199133109567008501

theorem tailTrace_5075436 : CollatzResearch.WordTrace tailWord_5075436 prefixEnd_5075436 2606138199133109567008501 := by
  unfold tailWord_5075436
  simp only [CollatzResearch.WordTrace]
  refine ⟨92558179420284831151603081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123410905893713108202137441 92558179420284831151603081)
  ·
    refine ⟨69418634565213623363702311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92558179420284831151603081 69418634565213623363702311)
    ·
      refine ⟨104127951847820435045553467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69418634565213623363702311 104127951847820435045553467)
      ·
        refine ⟨156191927771730652568330201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104127951847820435045553467 156191927771730652568330201)
        ·
          refine ⟨117143945828797989426247651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156191927771730652568330201 117143945828797989426247651)
          ·
            refine ⟨175715918743196984139371477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117143945828797989426247651 175715918743196984139371477)
            ·
              refine ⟨4118341845543679315766519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 175715918743196984139371477 4118341845543679315766519)
              ·
                refine ⟨6177512768315518973649779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118341845543679315766519 6177512768315518973649779)
                ·
                  refine ⟨9266269152473278460474669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6177512768315518973649779 9266269152473278460474669)
                  ·
                    refine ⟨3474850932177479422678001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9266269152473278460474669 3474850932177479422678001)
                    ·
                      refine ⟨2606138199133109567008501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474850932177479422678001 2606138199133109567008501)
                      ·
                        rfl

theorem cell23_5075436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_5075436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075436 prefixEnd_5075436 := by exact prefixLift 5075436
  have htrace : WordTrace (prefixWord ++ tailWord_5075436) baseStart_5075436 baseEnd_5075436 := by
    simpa [prefixWord, tailWord_5075436, baseEnd_5075436] using wordTrace_append hprefix tailTrace_5075436
  have hstable : (prefixWord ++ tailWord_5075436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075436).length < 2 ^ (prefixWord ++ tailWord_5075436).sum := by decide
  have hdescent : baseEnd_5075436 < baseStart_5075436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075449 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 4, 2, 2]
def baseStart_5075449 : Nat := 118140960795 + 5075449 * 2 ^ 59
def prefixEnd_5075449 : Nat := 4983230072969 + 3 ^ 40 * 5075449 * 2
def baseEnd_5075449 : Nat := 2606144874381618016145941

theorem tailTrace_5075449 : CollatzResearch.WordTrace tailWord_5075449 prefixEnd_5075449 2606144874381618016145941 := by
  unfold tailWord_5075449
  simp only [CollatzResearch.WordTrace]
  refine ⟨185116832989522565523429401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123411221993015043682286267 185116832989522565523429401)
  ·
    refine ⟨138837624742141924142572051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185116832989522565523429401 138837624742141924142572051)
    ·
      refine ⟨208256437113212886213858077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138837624742141924142572051 208256437113212886213858077)
      ·
        refine ⟨78096163917454832330196779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208256437113212886213858077 78096163917454832330196779)
        ·
          refine ⟨117144245876182248495295169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78096163917454832330196779 117144245876182248495295169)
          ·
            refine ⟨87858184407136686371471377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117144245876182248495295169 87858184407136686371471377)
            ·
              refine ⟨65893638305352514778603533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87858184407136686371471377 65893638305352514778603533)
              ·
                refine ⟨24710114364507193041976325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65893638305352514778603533 24710114364507193041976325)
                ·
                  refine ⟨4633146443345098695370561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24710114364507193041976325 4633146443345098695370561)
                  ·
                    refine ⟨3474859832508824021527921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633146443345098695370561 3474859832508824021527921)
                    ·
                      refine ⟨2606144874381618016145941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474859832508824021527921 2606144874381618016145941)
                      ·
                        rfl

theorem cell23_5075449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_5075449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075449 prefixEnd_5075449 := by exact prefixLift 5075449
  have htrace : WordTrace (prefixWord ++ tailWord_5075449) baseStart_5075449 baseEnd_5075449 := by
    simpa [prefixWord, tailWord_5075449, baseEnd_5075449] using wordTrace_append hprefix tailTrace_5075449
  have hstable : (prefixWord ++ tailWord_5075449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075449).length < 2 ^ (prefixWord ++ tailWord_5075449).sum := by decide
  have hdescent : baseEnd_5075449 < baseStart_5075449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075455 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 7]
def baseStart_5075455 : Nat := 118140960795 + 5075455 * 2 ^ 59
def prefixEnd_5075455 : Nat := 4983230072969 + 3 ^ 40 * 5075455 * 2
def baseEnd_5075455 : Nat := 289571995029504999185657

theorem tailTrace_5075455 : CollatzResearch.WordTrace tailWord_5075455 prefixEnd_5075455 289571995029504999185657 := by
  unfold tailWord_5075455
  simp only [CollatzResearch.WordTrace]
  refine ⟨185117051827500828548147819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123411367885000552365431879 185117051827500828548147819)
  ·
    refine ⟨277675577741251242822221729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185117051827500828548147819 277675577741251242822221729)
    ·
      refine ⟨208256683305938432116666297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277675577741251242822221729 208256683305938432116666297)
      ·
        refine ⟨156192512479453824087499723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208256683305938432116666297 156192512479453824087499723)
        ·
          refine ⟨234288768719180736131249585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156192512479453824087499723 234288768719180736131249585)
          ·
            refine ⟨175716576539385552098437189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234288768719180736131249585 175716576539385552098437189)
            ·
              refine ⟨32946858101134791018456973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175716576539385552098437189 32946858101134791018456973)
              ·
                refine ⟨12355071787925546631921365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32946858101134791018456973 12355071787925546631921365)
                ·
                  refine ⟨289571995029504999185657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12355071787925546631921365 289571995029504999185657)
                  ·
                    rfl

theorem cell23_5075455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 7].length) (baseStart_5075455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075455 prefixEnd_5075455 := by exact prefixLift 5075455
  have htrace : WordTrace (prefixWord ++ tailWord_5075455) baseStart_5075455 baseEnd_5075455 := by
    simpa [prefixWord, tailWord_5075455, baseEnd_5075455] using wordTrace_append hprefix tailTrace_5075455
  have hstable : (prefixWord ++ tailWord_5075455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075455).length < 2 ^ (prefixWord ++ tailWord_5075455).sum := by decide
  have hdescent : baseEnd_5075455 < baseStart_5075455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075466 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_5075466 : Nat := 118140960795 + 5075466 * 2 ^ 59
def prefixEnd_5075466 : Nat := 4983230072969 + 3 ^ 40 * 5075466 * 2
def baseEnd_5075466 : Nat := 2606153603552744449633363

theorem tailTrace_5075466 : CollatzResearch.WordTrace tailWord_5075466 prefixEnd_5075466 2606153603552744449633363 := by
  unfold tailWord_5075466
  simp only [CollatzResearch.WordTrace]
  refine ⟨46279363257615244356699563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123411635353640651617865501 46279363257615244356699563)
  ·
    refine ⟨69419044886422866535049345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46279363257615244356699563 69419044886422866535049345)
    ·
      refine ⟨52064283664817149901287009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69419044886422866535049345 52064283664817149901287009)
      ·
        refine ⟨39048212748612862425965257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52064283664817149901287009 39048212748612862425965257)
        ·
          refine ⟨29286159561459646819473943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39048212748612862425965257 29286159561459646819473943)
          ·
            refine ⟨43929239342189470229210915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29286159561459646819473943 43929239342189470229210915)
            ·
              refine ⟨65893859013284205343816373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43929239342189470229210915 65893859013284205343816373)
              ·
                refine ⟨6177549282495394250982785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65893859013284205343816373 6177549282495394250982785)
                ·
                  refine ⟨4633161961871545688237089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177549282495394250982785 4633161961871545688237089)
                  ·
                    refine ⟨3474871471403659266177817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633161961871545688237089 3474871471403659266177817)
                    ·
                      refine ⟨2606153603552744449633363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474871471403659266177817 2606153603552744449633363)
                      ·
                        rfl

theorem cell23_5075466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_5075466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075466 prefixEnd_5075466 := by exact prefixLift 5075466
  have htrace : WordTrace (prefixWord ++ tailWord_5075466) baseStart_5075466 baseEnd_5075466 := by
    simpa [prefixWord, tailWord_5075466, baseEnd_5075466] using wordTrace_append hprefix tailTrace_5075466
  have hstable : (prefixWord ++ tailWord_5075466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075466).length < 2 ^ (prefixWord ++ tailWord_5075466).sum := by decide
  have hdescent : baseEnd_5075466 < baseStart_5075466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075489 : List Nat := [1, 2, 3, 2, 2, 1, 4, 3, 5]
def baseStart_5075489 : Nat := 118140960795 + 5075489 * 2 ^ 59
def prefixEnd_5075489 : Nat := 4983230072969 + 3 ^ 40 * 5075489 * 2
def baseEnd_5075489 : Nat := 289573934845310873293973

theorem tailTrace_5075489 : CollatzResearch.WordTrace tailWord_5075489 prefixEnd_5075489 289573934845310873293973 := by
  unfold tailWord_5075489
  simp only [CollatzResearch.WordTrace]
  refine ⟨185118291909377652354885521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123412194606251768236590347 185118291909377652354885521)
  ·
    refine ⟨138838718932033239266164141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185118291909377652354885521 138838718932033239266164141)
    ·
      refine ⟨52064519599512464724811553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138838718932033239266164141 52064519599512464724811553)
      ·
        refine ⟨39048389699634348543608665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52064519599512464724811553 39048389699634348543608665)
        ·
          refine ⟨29286292274725761407706499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39048389699634348543608665 29286292274725761407706499)
          ·
            refine ⟨43929438412088642111559749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29286292274725761407706499 43929438412088642111559749)
            ·
              refine ⟨8236769702266620395917453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43929438412088642111559749 8236769702266620395917453)
              ·
                refine ⟨3088788638349982648469045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8236769702266620395917453 3088788638349982648469045)
                ·
                  refine ⟨289573934845310873293973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3088788638349982648469045 289573934845310873293973)
                  ·
                    rfl

theorem cell23_5075489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 5].length) (baseStart_5075489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075489 prefixEnd_5075489 := by exact prefixLift 5075489
  have htrace : WordTrace (prefixWord ++ tailWord_5075489) baseStart_5075489 baseEnd_5075489 := by
    simpa [prefixWord, tailWord_5075489, baseEnd_5075489] using wordTrace_append hprefix tailTrace_5075489
  have hstable : (prefixWord ++ tailWord_5075489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075489).length < 2 ^ (prefixWord ++ tailWord_5075489).sum := by decide
  have hdescent : baseEnd_5075489 < baseStart_5075489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075562 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 8]
def baseStart_5075562 : Nat := 118140960795 + 5075562 * 2 ^ 59
def prefixEnd_5075562 : Nat := 4983230072969 + 3 ^ 40 * 5075562 * 2
def baseEnd_5075562 : Nat := 289578099743952897114769

theorem tailTrace_5075562 : CollatzResearch.WordTrace tailWord_5075562 prefixEnd_5075562 289578099743952897114769 := by
  unfold tailWord_5075562
  simp only [CollatzResearch.WordTrace]
  refine ⟨46280238609528296455573235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123413969625408790548195293 46280238609528296455573235)
  ·
    refine ⟨69420357914292444683359853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46280238609528296455573235 69420357914292444683359853)
    ·
      refine ⟨26032634217859666756259945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69420357914292444683359853 26032634217859666756259945)
      ·
        refine ⟨19524475663394750067194959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26032634217859666756259945 19524475663394750067194959)
        ·
          refine ⟨29286713495092125100792439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19524475663394750067194959 29286713495092125100792439)
          ·
            refine ⟨43930070242638187651188659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29286713495092125100792439 43930070242638187651188659)
            ·
              refine ⟨65895105363957281476782989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43930070242638187651188659 65895105363957281476782989)
              ·
                refine ⟨24710664511483980553793621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65895105363957281476782989 24710664511483980553793621)
                ·
                  refine ⟨289578099743952897114769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24710664511483980553793621 289578099743952897114769)
                  ·
                    rfl

theorem cell23_5075562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_5075562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075562 prefixEnd_5075562 := by exact prefixLift 5075562
  have htrace : WordTrace (prefixWord ++ tailWord_5075562) baseStart_5075562 baseEnd_5075562 := by
    simpa [prefixWord, tailWord_5075562, baseEnd_5075562] using wordTrace_append hprefix tailTrace_5075562
  have hstable : (prefixWord ++ tailWord_5075562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075562).length < 2 ^ (prefixWord ++ tailWord_5075562).sum := by decide
  have hdescent : baseEnd_5075562 < baseStart_5075562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075566 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_5075566 : Nat := 118140960795 + 5075566 * 2 ^ 59
def prefixEnd_5075566 : Nat := 4983230072969 + 3 ^ 40 * 5075566 * 2
def baseEnd_5075566 : Nat := 868734983872731352794301

theorem tailTrace_5075566 : CollatzResearch.WordTrace tailWord_5075566 prefixEnd_5075566 868734983872731352794301 := by
  unfold tailWord_5075566
  simp only [CollatzResearch.WordTrace]
  refine ⟨23140137541262336813179819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123414066886732463003625701 23140137541262336813179819)
  ·
    refine ⟨34710206311893505219769729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23140137541262336813179819 34710206311893505219769729)
    ·
      refine ⟨26032654733920128914827297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34710206311893505219769729 26032654733920128914827297)
      ·
        refine ⟨19524491050440096686120473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26032654733920128914827297 19524491050440096686120473)
        ·
          refine ⟨14643368287830072514590355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19524491050440096686120473 14643368287830072514590355)
          ·
            refine ⟨21965052431745108771885533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14643368287830072514590355 21965052431745108771885533)
            ·
              refine ⟨8236894661904415789457075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21965052431745108771885533 8236894661904415789457075)
              ·
                refine ⟨12355341992856623684185613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8236894661904415789457075 12355341992856623684185613)
                ·
                  refine ⟨4633253247321233881569605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12355341992856623684185613 4633253247321233881569605)
                  ·
                    refine ⟨868734983872731352794301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4633253247321233881569605 868734983872731352794301)
                    ·
                      rfl

theorem cell23_5075566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_5075566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075566 prefixEnd_5075566 := by exact prefixLift 5075566
  have htrace : WordTrace (prefixWord ++ tailWord_5075566) baseStart_5075566 baseEnd_5075566 := by
    simpa [prefixWord, tailWord_5075566, baseEnd_5075566] using wordTrace_append hprefix tailTrace_5075566
  have hstable : (prefixWord ++ tailWord_5075566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075566).length < 2 ^ (prefixWord ++ tailWord_5075566).sum := by decide
  have hdescent : baseEnd_5075566 < baseStart_5075566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075599 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 6, 3, 2]
def baseStart_5075599 : Nat := 118140960795 + 5075599 * 2 ^ 59
def prefixEnd_5075599 : Nat := 4983230072969 + 3 ^ 40 * 5075599 * 2
def baseEnd_5075599 : Nat := 2606221896479792429270251

theorem tailTrace_5075599 : CollatzResearch.WordTrace tailWord_5075599 prefixEnd_5075599 2606221896479792429270251 := by
  unfold tailWord_5075599
  simp only [CollatzResearch.WordTrace]
  refine ⟨185122303938979141141389851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123414869292652760760926567 185122303938979141141389851)
  ·
    refine ⟨277683455908468711712084777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185122303938979141141389851 277683455908468711712084777)
    ·
      refine ⟨208262591931351533784063583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277683455908468711712084777 208262591931351533784063583)
      ·
        refine ⟨312393887897027300676095375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208262591931351533784063583 312393887897027300676095375)
        ·
          refine ⟨468590831845540951014143063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312393887897027300676095375 468590831845540951014143063)
          ·
            refine ⟨702886247768311426521214595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468590831845540951014143063 702886247768311426521214595)
            ·
              refine ⟨1054329371652467139781821893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702886247768311426521214595 1054329371652467139781821893)
              ·
                refine ⟨197686757184837588709091605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1054329371652467139781821893 197686757184837588709091605)
                ·
                  refine ⟨9266566743039261970738669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 197686757184837588709091605 9266566743039261970738669)
                  ·
                    refine ⟨3474962528639723239027001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9266566743039261970738669 3474962528639723239027001)
                    ·
                      refine ⟨2606221896479792429270251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3474962528639723239027001 2606221896479792429270251)
                      ·
                        rfl

theorem cell23_5075599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3, 2].length) (baseStart_5075599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075599 prefixEnd_5075599 := by exact prefixLift 5075599
  have htrace : WordTrace (prefixWord ++ tailWord_5075599) baseStart_5075599 baseEnd_5075599 := by
    simpa [prefixWord, tailWord_5075599, baseEnd_5075599] using wordTrace_append hprefix tailTrace_5075599
  have hstable : (prefixWord ++ tailWord_5075599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075599).length < 2 ^ (prefixWord ++ tailWord_5075599).sum := by decide
  have hdescent : baseEnd_5075599 < baseStart_5075599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075617 : List Nat := [1, 2, 3, 3, 4, 1, 2, 2, 1, 4]
def baseStart_5075617 : Nat := 118140960795 + 5075617 * 2 ^ 59
def prefixEnd_5075617 : Nat := 4983230072969 + 3 ^ 40 * 5075617 * 2
def baseEnd_5075617 : Nat := 868743713043857786281723

theorem tailTrace_5075617 : CollatzResearch.WordTrace tailWord_5075617 prefixEnd_5075617 868743713043857786281723 := by
  unfold tailWord_5075617
  simp only [CollatzResearch.WordTrace]
  refine ⟨185122960452913930215545105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123415306968609286810363403 185122960452913930215545105)
  ·
    refine ⟨138842220339685447661658829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185122960452913930215545105 138842220339685447661658829)
    ·
      refine ⟨52065832627382042873122061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138842220339685447661658829 52065832627382042873122061)
      ·
        refine ⟨19524687235268266077420773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52065832627382042873122061 19524687235268266077420773)
        ·
          refine ⟨3660878856612799889516395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19524687235268266077420773 3660878856612799889516395)
          ·
            refine ⟨5491318284919199834274593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3660878856612799889516395 5491318284919199834274593)
            ·
              refine ⟨4118488713689399875705945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5491318284919199834274593 4118488713689399875705945)
              ·
                refine ⟨3088866535267049906779459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4118488713689399875705945 3088866535267049906779459)
                ·
                  refine ⟨4633299802900574860169189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088866535267049906779459 4633299802900574860169189)
                  ·
                    refine ⟨868743713043857786281723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4633299802900574860169189 868743713043857786281723)
                    ·
                      rfl

theorem cell23_5075617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_5075617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075617 prefixEnd_5075617 := by exact prefixLift 5075617
  have htrace : WordTrace (prefixWord ++ tailWord_5075617) baseStart_5075617 baseEnd_5075617 := by
    simpa [prefixWord, tailWord_5075617, baseEnd_5075617] using wordTrace_append hprefix tailTrace_5075617
  have hstable : (prefixWord ++ tailWord_5075617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075617).length < 2 ^ (prefixWord ++ tailWord_5075617).sum := by decide
  have hdescent : baseEnd_5075617 < baseStart_5075617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075632 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_5075632 : Nat := 118140960795 + 5075632 * 2 ^ 59
def prefixEnd_5075632 : Nat := 4983230072969 + 3 ^ 40 * 5075632 * 2
def baseEnd_5075632 : Nat := 2606238841341390800157599

theorem tailTrace_5075632 : CollatzResearch.WordTrace tailWord_5075632 prefixEnd_5075632 2606238841341390800157599 := by
  unfold tailWord_5075632
  simp only [CollatzResearch.WordTrace]
  refine ⟨92561753773929793888670575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123415671698573058518227433 92561753773929793888670575)
  ·
    refine ⟨138842630660894690833005863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92561753773929793888670575 138842630660894690833005863)
    ·
      refine ⟨208263945991342036249508795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138842630660894690833005863 208263945991342036249508795)
      ·
        refine ⟨312395918987013054374263193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208263945991342036249508795 312395918987013054374263193)
        ·
          refine ⟨234296939240259790780697395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312395918987013054374263193 234296939240259790780697395)
          ·
            refine ⟨351445408860389686171046093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234296939240259790780697395 351445408860389686171046093)
            ·
              refine ⟨131792028322646132314142285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351445408860389686171046093 131792028322646132314142285)
              ·
                refine ⟨49422010620992299617803357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131792028322646132314142285 49422010620992299617803357)
                ·
                  refine ⟨18533253982872112356676259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49422010620992299617803357 18533253982872112356676259)
                  ·
                    refine ⟨27799880974308168535014389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18533253982872112356676259 27799880974308168535014389)
                    ·
                      refine ⟨2606238841341390800157599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27799880974308168535014389 2606238841341390800157599)
                      ·
                        rfl

theorem cell23_5075632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_5075632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075632 prefixEnd_5075632 := by exact prefixLift 5075632
  have htrace : WordTrace (prefixWord ++ tailWord_5075632) baseStart_5075632 baseEnd_5075632 := by
    simpa [prefixWord, tailWord_5075632, baseEnd_5075632] using wordTrace_append hprefix tailTrace_5075632
  have hstable : (prefixWord ++ tailWord_5075632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075632).length < 2 ^ (prefixWord ++ tailWord_5075632).sum := by decide
  have hdescent : baseEnd_5075632 < baseStart_5075632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075646 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_5075646 : Nat := 118140960795 + 5075646 * 2 ^ 59
def prefixEnd_5075646 : Nat := 4983230072969 + 3 ^ 40 * 5075646 * 2
def baseEnd_5075646 : Nat := 2606246030070553745382535

theorem tailTrace_5075646 : CollatzResearch.WordTrace tailWord_5075646 prefixEnd_5075646 2606246030070553745382535 := by
  unfold tailWord_5075646
  simp only [CollatzResearch.WordTrace]
  refine ⟨23140502271226108521043849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123416012113205912112233861 23140502271226108521043849)
  ·
    refine ⟨17355376703419581390782887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23140502271226108521043849 17355376703419581390782887)
    ·
      refine ⟨26033065055129372086174331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17355376703419581390782887 26033065055129372086174331)
      ·
        refine ⟨39049597582694058129261497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26033065055129372086174331 39049597582694058129261497)
        ·
          refine ⟨29287198187020543596946123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39049597582694058129261497 29287198187020543596946123)
          ·
            refine ⟨43930797280530815395419185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29287198187020543596946123 43930797280530815395419185)
            ·
              refine ⟨32948097960398111546564389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43930797280530815395419185 32948097960398111546564389)
              ·
                refine ⟨6177768367574645914980823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32948097960398111546564389 6177768367574645914980823)
                ·
                  refine ⟨9266652551361968872471235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6177768367574645914980823 9266652551361968872471235)
                  ·
                    refine ⟨13899978827042953308706853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9266652551361968872471235 13899978827042953308706853)
                    ·
                      refine ⟨2606246030070553745382535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13899978827042953308706853 2606246030070553745382535)
                      ·
                        rfl

theorem cell23_5075646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_5075646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075646 prefixEnd_5075646 := by exact prefixLift 5075646
  have htrace : WordTrace (prefixWord ++ tailWord_5075646) baseStart_5075646 baseEnd_5075646 := by
    simpa [prefixWord, tailWord_5075646, baseEnd_5075646] using wordTrace_append hprefix tailTrace_5075646
  have hstable : (prefixWord ++ tailWord_5075646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075646).length < 2 ^ (prefixWord ++ tailWord_5075646).sum := by decide
  have hdescent : baseEnd_5075646 < baseStart_5075646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075706 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2]
def baseStart_5075706 : Nat := 118140960795 + 5075706 * 2 ^ 59
def prefixEnd_5075706 : Nat := 4983230072969 + 3 ^ 40 * 5075706 * 2
def baseEnd_5075706 : Nat := 2606276838909823510632259

theorem tailTrace_5075706 : CollatzResearch.WordTrace tailWord_5075706 prefixEnd_5075706 2606276838909823510632259 := by
  unfold tailWord_5075706
  simp only [CollatzResearch.WordTrace]
  refine ⟨46281551637397874603883743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123417471033060998943689981 46281551637397874603883743)
  ·
    refine ⟨69422327456096811905825615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46281551637397874603883743 69422327456096811905825615)
    ·
      refine ⟨104133491184145217858738423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69422327456096811905825615 104133491184145217858738423)
      ·
        refine ⟨156200236776217826788107635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104133491184145217858738423 156200236776217826788107635)
        ·
          refine ⟨234300355164326740182161453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156200236776217826788107635 234300355164326740182161453)
          ·
            refine ⟨87862633186622527568310545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234300355164326740182161453 87862633186622527568310545)
            ·
              refine ⟨65896974889966895676232909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87862633186622527568310545 65896974889966895676232909)
              ·
                refine ⟨24711365583737585878587341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65896974889966895676232909 24711365583737585878587341)
                ·
                  refine ⟨9266762093901594704470253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24711365583737585878587341 9266762093901594704470253)
                  ·
                    refine ⟨3475035785213098014176345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9266762093901594704470253 3475035785213098014176345)
                    ·
                      refine ⟨2606276838909823510632259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475035785213098014176345 2606276838909823510632259)
                      ·
                        rfl

theorem cell23_5075706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_5075706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075706 prefixEnd_5075706 := by exact prefixLift 5075706
  have htrace : WordTrace (prefixWord ++ tailWord_5075706) baseStart_5075706 baseEnd_5075706 := by
    simpa [prefixWord, tailWord_5075706, baseEnd_5075706] using wordTrace_append hprefix tailTrace_5075706
  have hstable : (prefixWord ++ tailWord_5075706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075706).length < 2 ^ (prefixWord ++ tailWord_5075706).sum := by decide
  have hdescent : baseEnd_5075706 < baseStart_5075706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075714 : List Nat := [3, 4, 1, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_5075714 : Nat := 118140960795 + 5075714 * 2 ^ 59
def prefixEnd_5075714 : Nat := 4983230072969 + 3 ^ 40 * 5075714 * 2
def baseEnd_5075714 : Nat := 2606280946755059479332223

theorem tailTrace_5075714 : CollatzResearch.WordTrace tailWord_5075714 prefixEnd_5075714 2606280946755059479332223 := by
  unfold tailWord_5075714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46281624583390628945456549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123417665555708343854550797 46281624583390628945456549)
  ·
    refine ⟨8677804609385742927273103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46281624583390628945456549 8677804609385742927273103)
    ·
      refine ⟨13016706914078614390909655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8677804609385742927273103 13016706914078614390909655)
      ·
        refine ⟨19525060371117921586364483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13016706914078614390909655 19525060371117921586364483)
        ·
          refine ⟨29287590556676882379546725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19525060371117921586364483 29287590556676882379546725)
          ·
            refine ⟨5491423229376915446165011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29287590556676882379546725 5491423229376915446165011)
            ·
              refine ⟨8237134844065373169247517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5491423229376915446165011 8237134844065373169247517)
              ·
                refine ⟨3088925566524514938467819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8237134844065373169247517 3088925566524514938467819)
                ·
                  refine ⟨4633388349786772407701729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088925566524514938467819 4633388349786772407701729)
                  ·
                    refine ⟨3475041262340079305776297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633388349786772407701729 3475041262340079305776297)
                    ·
                      refine ⟨2606280946755059479332223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475041262340079305776297 2606280946755059479332223)
                      ·
                        rfl

theorem cell23_5075714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_5075714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075714 prefixEnd_5075714 := by exact prefixLift 5075714
  have htrace : WordTrace (prefixWord ++ tailWord_5075714) baseStart_5075714 baseEnd_5075714 := by
    simpa [prefixWord, tailWord_5075714, baseEnd_5075714] using wordTrace_append hprefix tailTrace_5075714
  have hstable : (prefixWord ++ tailWord_5075714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075714).length < 2 ^ (prefixWord ++ tailWord_5075714).sum := by decide
  have hdescent : baseEnd_5075714 < baseStart_5075714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075749 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_5075749 : Nat := 118140960795 + 5075749 * 2 ^ 59
def prefixEnd_5075749 : Nat := 4983230072969 + 3 ^ 40 * 5075749 * 2
def baseEnd_5075749 : Nat := 2606298918577966842394561

theorem tailTrace_5075749 : CollatzResearch.WordTrace tailWord_5075749 prefixEnd_5075749 2606298918577966842394561 := by
  unfold tailWord_5075749
  simp only [CollatzResearch.WordTrace]
  refine ⟨185127774888435716759350301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123418516592290477839566867 185127774888435716759350301)
  ·
    refine ⟨69422915583163393784756363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185127774888435716759350301 69422915583163393784756363)
    ·
      refine ⟨104134373374745090677134545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69422915583163393784756363 104134373374745090677134545)
      ·
        refine ⟨78100780031058818007850909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104134373374745090677134545 78100780031058818007850909)
        ·
          refine ⟨29287792511647056752944091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78100780031058818007850909 29287792511647056752944091)
          ·
            refine ⟨43931688767470585129416137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29287792511647056752944091 43931688767470585129416137)
            ·
              refine ⟨32948766575602938847062103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43931688767470585129416137 32948766575602938847062103)
              ·
                refine ⟨49423149863404408270593155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32948766575602938847062103 49423149863404408270593155)
                ·
                  refine ⟨74134724795106612405889733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49423149863404408270593155 74134724795106612405889733)
                  ·
                    refine ⟨13900260899082489826104325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74134724795106612405889733 13900260899082489826104325)
                    ·
                      refine ⟨2606298918577966842394561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13900260899082489826104325 2606298918577966842394561)
                      ·
                        rfl

theorem cell23_5075749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_5075749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075749 prefixEnd_5075749 := by exact prefixLift 5075749
  have htrace : WordTrace (prefixWord ++ tailWord_5075749) baseStart_5075749 baseEnd_5075749 := by
    simpa [prefixWord, tailWord_5075749, baseEnd_5075749] using wordTrace_append hprefix tailTrace_5075749
  have hstable : (prefixWord ++ tailWord_5075749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075749).length < 2 ^ (prefixWord ++ tailWord_5075749).sum := by decide
  have hdescent : baseEnd_5075749 < baseStart_5075749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075753 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 2, 2, 2]
def baseStart_5075753 : Nat := 118140960795 + 5075753 * 2 ^ 59
def prefixEnd_5075753 : Nat := 4983230072969 + 3 ^ 40 * 5075753 * 2
def baseEnd_5075753 : Nat := 2606300972500584826744543

theorem tailTrace_5075753 : CollatzResearch.WordTrace tailWord_5075753 prefixEnd_5075753 2606300972500584826744543 := by
  unfold tailWord_5075753
  simp only [CollatzResearch.WordTrace]
  refine ⟨185127920780421225442495913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123418613853614150294997275 185127920780421225442495913)
  ·
    refine ⟨138845940585315919081871935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185127920780421225442495913 138845940585315919081871935)
    ·
      refine ⟨208268910877973878622807903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138845940585315919081871935 208268910877973878622807903)
      ·
        refine ⟨312403366316960817934211855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208268910877973878622807903 312403366316960817934211855)
        ·
          refine ⟨468605049475441226901317783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312403366316960817934211855 468605049475441226901317783)
          ·
            refine ⟨702907574213161840351976675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468605049475441226901317783 702907574213161840351976675)
            ·
              refine ⟨1054361361319742760527965013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702907574213161840351976675 1054361361319742760527965013)
              ·
                refine ⟨6177898601482867737468545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1054361361319742760527965013 6177898601482867737468545)
                ·
                  refine ⟨4633423951112150803101409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177898601482867737468545 4633423951112150803101409)
                  ·
                    refine ⟨3475067963334113102326057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633423951112150803101409 3475067963334113102326057)
                    ·
                      refine ⟨2606300972500584826744543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475067963334113102326057 2606300972500584826744543)
                      ·
                        rfl

theorem cell23_5075753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 2, 2].length) (baseStart_5075753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075753 prefixEnd_5075753 := by exact prefixLift 5075753
  have htrace : WordTrace (prefixWord ++ tailWord_5075753) baseStart_5075753 baseEnd_5075753 := by
    simpa [prefixWord, tailWord_5075753, baseEnd_5075753] using wordTrace_append hprefix tailTrace_5075753
  have hstable : (prefixWord ++ tailWord_5075753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075753).length < 2 ^ (prefixWord ++ tailWord_5075753).sum := by decide
  have hdescent : baseEnd_5075753 < baseStart_5075753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075757 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5075757 : Nat := 118140960795 + 5075757 * 2 ^ 59
def prefixEnd_5075757 : Nat := 4983230072969 + 3 ^ 40 * 5075757 * 2
def baseEnd_5075757 : Nat := 2606303026423202811094525

theorem tailTrace_5075757 : CollatzResearch.WordTrace tailWord_5075757 prefixEnd_5075757 2606303026423202811094525 := by
  unfold tailWord_5075757
  simp only [CollatzResearch.WordTrace]
  refine ⟨185128066672406734125641525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123418711114937822750427683 185128066672406734125641525)
  ·
    refine ⟨17355756250538131324278893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185128066672406734125641525 17355756250538131324278893)
    ·
      refine ⟨6508408593951799246604585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17355756250538131324278893 6508408593951799246604585)
      ·
        refine ⟨4881306445463849434953439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6508408593951799246604585 4881306445463849434953439)
        ·
          refine ⟨7321959668195774152430159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881306445463849434953439 7321959668195774152430159)
          ·
            refine ⟨10982939502293661228645239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7321959668195774152430159 10982939502293661228645239)
            ·
              refine ⟨16474409253440491842967859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10982939502293661228645239 16474409253440491842967859)
              ·
                refine ⟨24711613880160737764451789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16474409253440491842967859 24711613880160737764451789)
                ·
                  refine ⟨9266855205060276661669421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24711613880160737764451789 9266855205060276661669421)
                  ·
                    refine ⟨3475070701897603748126033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9266855205060276661669421 3475070701897603748126033)
                    ·
                      refine ⟨2606303026423202811094525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475070701897603748126033 2606303026423202811094525)
                      ·
                        rfl

theorem cell23_5075757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5075757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075757 prefixEnd_5075757 := by exact prefixLift 5075757
  have htrace : WordTrace (prefixWord ++ tailWord_5075757) baseStart_5075757 baseEnd_5075757 := by
    simpa [prefixWord, tailWord_5075757, baseEnd_5075757] using wordTrace_append hprefix tailTrace_5075757
  have hstable : (prefixWord ++ tailWord_5075757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075757).length < 2 ^ (prefixWord ++ tailWord_5075757).sum := by decide
  have hdescent : baseEnd_5075757 < baseStart_5075757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075793 : List Nat := [1, 2, 2, 1, 6, 1, 1, 4, 5]
def baseStart_5075793 : Nat := 118140960795 + 5075793 * 2 ^ 59
def prefixEnd_5075793 : Nat := 4983230072969 + 3 ^ 40 * 5075793 * 2
def baseEnd_5075793 : Nat := 289591279080751630027151

theorem tailTrace_5075793 : CollatzResearch.WordTrace tailWord_5075793 prefixEnd_5075793 289591279080751630027151 := by
  unfold tailWord_5075793
  simp only [CollatzResearch.WordTrace]
  refine ⟨185129379700276312273952033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123419586466850874849301355 185129379700276312273952033)
  ·
    refine ⟨138847034775207234205464025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185129379700276312273952033 138847034775207234205464025)
    ·
      refine ⟨104135276081405425654098019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138847034775207234205464025 104135276081405425654098019)
      ·
        refine ⟨156202914122108138481147029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104135276081405425654098019 156202914122108138481147029)
        ·
          refine ⟨7322011599473818991303767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 156202914122108138481147029 7322011599473818991303767)
          ·
            refine ⟨10983017399210728486955651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322011599473818991303767 10983017399210728486955651)
            ·
              refine ⟨16474526098816092730433477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10983017399210728486955651 16474526098816092730433477)
              ·
                refine ⟨3088973643528017386956277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16474526098816092730433477 3088973643528017386956277)
                ·
                  refine ⟨289591279080751630027151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3088973643528017386956277 289591279080751630027151)
                  ·
                    rfl

theorem cell23_5075793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 5].length) (baseStart_5075793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075793 prefixEnd_5075793 := by exact prefixLift 5075793
  have htrace : WordTrace (prefixWord ++ tailWord_5075793) baseStart_5075793 baseEnd_5075793 := by
    simpa [prefixWord, tailWord_5075793, baseEnd_5075793] using wordTrace_append hprefix tailTrace_5075793
  have hstable : (prefixWord ++ tailWord_5075793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075793).length < 2 ^ (prefixWord ++ tailWord_5075793).sum := by decide
  have hdescent : baseEnd_5075793 < baseStart_5075793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075839 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_5075839 : Nat := 118140960795 + 5075839 * 2 ^ 59
def prefixEnd_5075839 : Nat := 4983230072969 + 3 ^ 40 * 5075839 * 2
def baseEnd_5075839 : Nat := 2606345131836871490269147

theorem tailTrace_5075839 : CollatzResearch.WordTrace tailWord_5075839 prefixEnd_5075839 2606345131836871490269147 := by
  unfold tailWord_5075839
  simp only [CollatzResearch.WordTrace]
  refine ⟨185131057458109662130126571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123420704972073108086751047 185131057458109662130126571)
  ·
    refine ⟨277696586187164493195189857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185131057458109662130126571 277696586187164493195189857)
    ·
      refine ⟨208272439640373369896392393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277696586187164493195189857 208272439640373369896392393)
      ·
        refine ⟨156204329730280027422294295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208272439640373369896392393 156204329730280027422294295)
        ·
          refine ⟨234306494595420041133441443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156204329730280027422294295 234306494595420041133441443)
          ·
            refine ⟨351459741893130061700162165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234306494595420041133441443 351459741893130061700162165)
            ·
              refine ⟨32949350802480943284390203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 351459741893130061700162165 32949350802480943284390203)
              ·
                refine ⟨49424026203721414926585305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32949350802480943284390203 49424026203721414926585305)
                ·
                  refine ⟨37068019652791061194938979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49424026203721414926585305 37068019652791061194938979)
                  ·
                    refine ⟨55602029479186591792408469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37068019652791061194938979 55602029479186591792408469)
                    ·
                      refine ⟨2606345131836871490269147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55602029479186591792408469 2606345131836871490269147)
                      ·
                        rfl

theorem cell23_5075839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_5075839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075839 prefixEnd_5075839 := by exact prefixLift 5075839
  have htrace : WordTrace (prefixWord ++ tailWord_5075839) baseStart_5075839 baseEnd_5075839 := by
    simpa [prefixWord, tailWord_5075839, baseEnd_5075839] using wordTrace_append hprefix tailTrace_5075839
  have hstable : (prefixWord ++ tailWord_5075839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075839).length < 2 ^ (prefixWord ++ tailWord_5075839).sum := by decide
  have hdescent : baseEnd_5075839 < baseStart_5075839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075876 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_5075876 : Nat := 118140960795 + 5075876 * 2 ^ 59
def prefixEnd_5075876 : Nat := 4983230072969 + 3 ^ 40 * 5075876 * 2
def baseEnd_5075876 : Nat := 2606364130621087845506477

theorem tailTrace_5075876 : CollatzResearch.WordTrace tailWord_5075876 prefixEnd_5075876 2606364130621087845506477 := by
  unfold tailWord_5075876
  simp only [CollatzResearch.WordTrace]
  refine ⟨92566203479487808724611741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123421604639317078299482321 92566203479487808724611741)
  ·
    refine ⟨34712326304807928271729403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92566203479487808724611741 34712326304807928271729403)
    ·
      refine ⟨52068489457211892407594105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34712326304807928271729403 52068489457211892407594105)
      ·
        refine ⟨39051367092908919305695579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52068489457211892407594105 39051367092908919305695579)
        ·
          refine ⟨58577050639363378958543369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39051367092908919305695579 58577050639363378958543369)
          ·
            refine ⟨43932787979522534218907527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58577050639363378958543369 43932787979522534218907527)
            ·
              refine ⟨65899181969283801328361291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43932787979522534218907527 65899181969283801328361291)
              ·
                refine ⟨98848772953925701992541937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65899181969283801328361291 98848772953925701992541937)
                ·
                  refine ⟨74136579715444276494406453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98848772953925701992541937 74136579715444276494406453)
                  ·
                    refine ⟨6950304348322900921350605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74136579715444276494406453 6950304348322900921350605)
                    ·
                      refine ⟨2606364130621087845506477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6950304348322900921350605 2606364130621087845506477)
                      ·
                        rfl

theorem cell23_5075876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_5075876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075876 prefixEnd_5075876 := by exact prefixLift 5075876
  have htrace : WordTrace (prefixWord ++ tailWord_5075876) baseStart_5075876 baseEnd_5075876 := by
    simpa [prefixWord, tailWord_5075876, baseEnd_5075876] using wordTrace_append hprefix tailTrace_5075876
  have hstable : (prefixWord ++ tailWord_5075876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075876).length < 2 ^ (prefixWord ++ tailWord_5075876).sum := by decide
  have hdescent : baseEnd_5075876 < baseStart_5075876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075894 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5075894 : Nat := 118140960795 + 5075894 * 2 ^ 59
def prefixEnd_5075894 : Nat := 4983230072969 + 3 ^ 40 * 5075894 * 2
def baseEnd_5075894 : Nat := 2606373373272868775081395

theorem tailTrace_5075894 : CollatzResearch.WordTrace tailWord_5075894 prefixEnd_5075894 2606373373272868775081395 := by
  unfold tailWord_5075894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11570816467056900407711171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123422042315273604348919157 11570816467056900407711171)
  ·
    refine ⟨17356224700585350611566757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11570816467056900407711171 17356224700585350611566757)
    ·
      refine ⟨3254292131359753239668767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17356224700585350611566757 3254292131359753239668767)
      ·
        refine ⟨4881438197039629859503151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254292131359753239668767 4881438197039629859503151)
        ·
          refine ⟨7322157295559444789254727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881438197039629859503151 7322157295559444789254727)
          ·
            refine ⟨10983235943339167183882091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322157295559444789254727 10983235943339167183882091)
            ·
              refine ⟨16474853915008750775823137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10983235943339167183882091 16474853915008750775823137)
              ·
                refine ⟨12356140436256563081867353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16474853915008750775823137 12356140436256563081867353)
                ·
                  refine ⟨9267105327192422311400515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12356140436256563081867353 9267105327192422311400515)
                  ·
                    refine ⟨13900657990788633467100773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9267105327192422311400515 13900657990788633467100773)
                    ·
                      refine ⟨2606373373272868775081395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13900657990788633467100773 2606373373272868775081395)
                      ·
                        rfl

theorem cell23_5075894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5075894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075894 prefixEnd_5075894 := by exact prefixLift 5075894
  have htrace : WordTrace (prefixWord ++ tailWord_5075894) baseStart_5075894 baseEnd_5075894 := by
    simpa [prefixWord, tailWord_5075894, baseEnd_5075894] using wordTrace_append hprefix tailTrace_5075894
  have hstable : (prefixWord ++ tailWord_5075894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075894).length < 2 ^ (prefixWord ++ tailWord_5075894).sum := by decide
  have hdescent : baseEnd_5075894 < baseStart_5075894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075930 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_5075930 : Nat := 118140960795 + 5075930 * 2 ^ 59
def prefixEnd_5075930 : Nat := 4983230072969 + 3 ^ 40 * 5075930 * 2
def baseEnd_5075930 : Nat := 868797286192143544743743

theorem tailTrace_5075930 : CollatzResearch.WordTrace tailWord_5075930 prefixEnd_5075930 868797286192143544743743 := by
  unfold tailWord_5075930
  simp only [CollatzResearch.WordTrace]
  refine ⟨46283594125194996167922311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123422917667186656447792829 46283594125194996167922311)
  ·
    refine ⟨69425391187792494251883467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46283594125194996167922311 69425391187792494251883467)
    ·
      refine ⟨104138086781688741377825201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69425391187792494251883467 104138086781688741377825201)
      ·
        refine ⟨78103565086266556033368901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104138086781688741377825201 78103565086266556033368901)
        ·
          refine ⟨14644418453674979256256669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78103565086266556033368901 14644418453674979256256669)
          ·
            refine ⟨5491656920128117221096251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14644418453674979256256669 5491656920128117221096251)
            ·
              refine ⟨8237485380192175831644377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5491656920128117221096251 8237485380192175831644377)
              ·
                refine ⟨6178114035144131873733283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8237485380192175831644377 6178114035144131873733283)
                ·
                  refine ⟨9267171052716197810599925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6178114035144131873733283 9267171052716197810599925)
                  ·
                    refine ⟨868797286192143544743743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9267171052716197810599925 868797286192143544743743)
                    ·
                      rfl

theorem cell23_5075930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_5075930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075930 prefixEnd_5075930 := by exact prefixLift 5075930
  have htrace : WordTrace (prefixWord ++ tailWord_5075930) baseStart_5075930 baseEnd_5075930 := by
    simpa [prefixWord, tailWord_5075930, baseEnd_5075930] using wordTrace_append hprefix tailTrace_5075930
  have hstable : (prefixWord ++ tailWord_5075930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075930).length < 2 ^ (prefixWord ++ tailWord_5075930).sum := by decide
  have hdescent : baseEnd_5075930 < baseStart_5075930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075943 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 1, 6]
def baseStart_5075943 : Nat := 118140960795 + 5075943 * 2 ^ 59
def prefixEnd_5075943 : Nat := 4983230072969 + 3 ^ 40 * 5075943 * 2
def baseEnd_5075943 : Nat := 868799511274979694456223

theorem tailTrace_5075943 : CollatzResearch.WordTrace tailWord_5075943 prefixEnd_5075943 868799511274979694456223 := by
  unfold tailWord_5075943
  simp only [CollatzResearch.WordTrace]
  refine ⟨185134850649732887891912483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123423233766488591927941655 185134850649732887891912483)
  ·
    refine ⟨277702275974599331837868725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185134850649732887891912483 277702275974599331837868725)
    ·
      refine ⟨26034588372618687359800193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277702275974599331837868725 26034588372618687359800193)
      ·
        refine ⟨19525941279464015519850145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26034588372618687359800193 19525941279464015519850145)
        ·
          refine ⟨14644455959598011639887609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19525941279464015519850145 14644455959598011639887609)
          ·
            refine ⟨10983341969698508729915707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14644455959598011639887609 10983341969698508729915707)
            ·
              refine ⟨16475012954547763094873561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10983341969698508729915707 16475012954547763094873561)
              ·
                refine ⟨12356259715910822321155171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16475012954547763094873561 12356259715910822321155171)
                ·
                  refine ⟨18534389573866233481732757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12356259715910822321155171 18534389573866233481732757)
                  ·
                    refine ⟨868799511274979694456223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18534389573866233481732757 868799511274979694456223)
                    ·
                      rfl

theorem cell23_5075943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_5075943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075943 prefixEnd_5075943 := by exact prefixLift 5075943
  have htrace : WordTrace (prefixWord ++ tailWord_5075943) baseStart_5075943 baseEnd_5075943 := by
    simpa [prefixWord, tailWord_5075943, baseEnd_5075943] using wordTrace_append hprefix tailTrace_5075943
  have hstable : (prefixWord ++ tailWord_5075943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075943).length < 2 ^ (prefixWord ++ tailWord_5075943).sum := by decide
  have hdescent : baseEnd_5075943 < baseStart_5075943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5075953 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_5075953 : Nat := 118140960795 + 5075953 * 2 ^ 59
def prefixEnd_5075953 : Nat := 4983230072969 + 3 ^ 40 * 5075953 * 2
def baseEnd_5075953 : Nat := 2606403668631484044243623

theorem tailTrace_5075953 : CollatzResearch.WordTrace tailWord_5075953 prefixEnd_5075953 2606403668631484044243623 := by
  unfold tailWord_5075953
  simp only [CollatzResearch.WordTrace]
  refine ⟨185135215379696659599776513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123423476919797773066517675 185135215379696659599776513)
  ·
    refine ⟨138851411534772494699832385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185135215379696659599776513 138851411534772494699832385)
    ·
      refine ⟨104138558651079371024874289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138851411534772494699832385 104138558651079371024874289)
      ·
        refine ⟨78103918988309528268655717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104138558651079371024874289 78103918988309528268655717)
        ·
          refine ⟨14644484810308036550372947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78103918988309528268655717 14644484810308036550372947)
          ·
            refine ⟨21966727215462054825559421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14644484810308036550372947 21966727215462054825559421)
            ·
              refine ⟨8237522705798270559584783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21966727215462054825559421 8237522705798270559584783)
              ·
                refine ⟨12356284058697405839377175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8237522705798270559584783 12356284058697405839377175)
                ·
                  refine ⟨18534426088046108759065763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12356284058697405839377175 18534426088046108759065763)
                  ·
                    refine ⟨27801639132069163138598645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18534426088046108759065763 27801639132069163138598645)
                    ·
                      refine ⟨2606403668631484044243623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27801639132069163138598645 2606403668631484044243623)
                      ·
                        rfl

theorem cell23_5075953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_5075953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5075953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5075953 prefixEnd_5075953 := by exact prefixLift 5075953
  have htrace : WordTrace (prefixWord ++ tailWord_5075953) baseStart_5075953 baseEnd_5075953 := by
    simpa [prefixWord, tailWord_5075953, baseEnd_5075953] using wordTrace_append hprefix tailTrace_5075953
  have hstable : (prefixWord ++ tailWord_5075953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5075953).length < 2 ^ (prefixWord ++ tailWord_5075953).sum := by decide
  have hdescent : baseEnd_5075953 < baseStart_5075953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5075953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076004 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5076004 : Nat := 118140960795 + 5076004 * 2 ^ 59
def prefixEnd_5076004 : Nat := 4983230072969 + 3 ^ 40 * 5076004 * 2
def baseEnd_5076004 : Nat := 2606429856144863344705889

theorem tailTrace_5076004 : CollatzResearch.WordTrace tailWord_5076004 prefixEnd_5076004 2606429856144863344705889 := by
  unfold tailWord_5076004
  simp only [CollatzResearch.WordTrace]
  refine ⟨92568537751255947654941533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123424717001674596873255377 92568537751255947654941533)
  ·
    refine ⟨34713201656720980370603075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92568537751255947654941533 34713201656720980370603075)
    ·
      refine ⟨52069802485081470555904613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34713201656720980370603075 52069802485081470555904613)
      ·
        refine ⟨9763087965952775729232115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52069802485081470555904613 9763087965952775729232115)
        ·
          refine ⟨14644631948929163593848173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9763087965952775729232115 14644631948929163593848173)
          ·
            refine ⟨5491736980848436347693065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14644631948929163593848173 5491736980848436347693065)
            ·
              refine ⟨4118802735636327260769799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5491736980848436347693065 4118802735636327260769799)
              ·
                refine ⟨6178204103454490891154699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118802735636327260769799 6178204103454490891154699)
                ·
                  refine ⟨9267306155181736336732049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6178204103454490891154699 9267306155181736336732049)
                  ·
                    refine ⟨6950479616386302252549037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9267306155181736336732049 6950479616386302252549037)
                    ·
                      refine ⟨2606429856144863344705889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6950479616386302252549037 2606429856144863344705889)
                      ·
                        rfl

theorem cell23_5076004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5076004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076004 prefixEnd_5076004 := by exact prefixLift 5076004
  have htrace : WordTrace (prefixWord ++ tailWord_5076004) baseStart_5076004 baseEnd_5076004 := by
    simpa [prefixWord, tailWord_5076004, baseEnd_5076004] using wordTrace_append hprefix tailTrace_5076004
  have hstable : (prefixWord ++ tailWord_5076004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076004).length < 2 ^ (prefixWord ++ tailWord_5076004).sum := by decide
  have hdescent : baseEnd_5076004 < baseStart_5076004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076016 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 4, 6]
def baseStart_5076016 : Nat := 118140960795 + 5076016 * 2 ^ 59
def prefixEnd_5076016 : Nat := 4983230072969 + 3 ^ 40 * 5076016 * 2
def baseEnd_5076016 : Nat := 868812005970905765918611

theorem tailTrace_5076016 : CollatzResearch.WordTrace tailWord_5076016 prefixEnd_5076016 868812005970905765918611 := by
  unfold tailWord_5076016
  simp only [CollatzResearch.WordTrace]
  refine ⟨92568756589234210679659951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123425008785645614239546601 92568756589234210679659951)
  ·
    refine ⟨138853134883851316019489927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92568756589234210679659951 138853134883851316019489927)
    ·
      refine ⟨208279702325776974029234891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138853134883851316019489927 208279702325776974029234891)
      ·
        refine ⟨312419553488665461043852337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208279702325776974029234891 312419553488665461043852337)
        ·
          refine ⟨234314665116499095782889253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312419553488665461043852337 234314665116499095782889253)
          ·
            refine ⟨43933999709343580459291735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234314665116499095782889253 43933999709343580459291735)
            ·
              refine ⟨65900999564015370688937603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43933999709343580459291735 65900999564015370688937603)
              ·
                refine ⟨98851499346023056033406405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65900999564015370688937603 98851499346023056033406405)
                ·
                  refine ⟨18534656127379323006263701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98851499346023056033406405 18534656127379323006263701)
                  ·
                    refine ⟨868812005970905765918611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18534656127379323006263701 868812005970905765918611)
                    ·
                      rfl

theorem cell23_5076016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_5076016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076016 prefixEnd_5076016 := by exact prefixLift 5076016
  have htrace : WordTrace (prefixWord ++ tailWord_5076016) baseStart_5076016 baseEnd_5076016 := by
    simpa [prefixWord, tailWord_5076016, baseEnd_5076016] using wordTrace_append hprefix tailTrace_5076016
  have hstable : (prefixWord ++ tailWord_5076016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076016).length < 2 ^ (prefixWord ++ tailWord_5076016).sum := by decide
  have hdescent : baseEnd_5076016 < baseStart_5076016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076093 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_5076093 : Nat := 118140960795 + 5076093 * 2 ^ 59
def prefixEnd_5076093 : Nat := 4983230072969 + 3 ^ 40 * 5076093 * 2
def baseEnd_5076093 : Nat := 868825185307704498830993

theorem tailTrace_5076093 : CollatzResearch.WordTrace tailWord_5076093 prefixEnd_5076093 868825185307704498830993 := by
  unfold tailWord_5076093
  simp only [CollatzResearch.WordTrace]
  refine ⟨185140321599189463509872933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123426881066126309006581955 185140321599189463509872933)
  ·
    refine ⟨34713810299848024408101175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185140321599189463509872933 34713810299848024408101175)
    ·
      refine ⟨52070715449772036612151763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34713810299848024408101175 52070715449772036612151763)
      ·
        refine ⟨78106073174658054918227645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52070715449772036612151763 78106073174658054918227645)
        ·
          refine ⟨29289777440496770594335367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78106073174658054918227645 29289777440496770594335367)
          ·
            refine ⟨43934666160745155891503051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29289777440496770594335367 43934666160745155891503051)
            ·
              refine ⟨65901999241117733837254577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43934666160745155891503051 65901999241117733837254577)
              ·
                refine ⟨49426499430838300377940933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65901999241117733837254577 49426499430838300377940933)
                ·
                  refine ⟨9267468643282181320863925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49426499430838300377940933 9267468643282181320863925)
                  ·
                    refine ⟨868825185307704498830993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9267468643282181320863925 868825185307704498830993)
                    ·
                      rfl

theorem cell23_5076093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_5076093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076093 prefixEnd_5076093 := by exact prefixLift 5076093
  have htrace : WordTrace (prefixWord ++ tailWord_5076093) baseStart_5076093 baseEnd_5076093 := by
    simpa [prefixWord, tailWord_5076093, baseEnd_5076093] using wordTrace_append hprefix tailTrace_5076093
  have hstable : (prefixWord ++ tailWord_5076093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076093).length < 2 ^ (prefixWord ++ tailWord_5076093).sum := by decide
  have hdescent : baseEnd_5076093 < baseStart_5076093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076110 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_5076110 : Nat := 118140960795 + 5076110 * 2 ^ 59
def prefixEnd_5076110 : Nat := 4983230072969 + 3 ^ 40 * 5076110 * 2
def baseEnd_5076110 : Nat := 868828095031413309993467

theorem tailTrace_5076110 : CollatzResearch.WordTrace tailWord_5076110 prefixEnd_5076110 868828095031413309993467 := by
  unfold tailWord_5076110
  simp only [CollatzResearch.WordTrace]
  refine ⟨23142617705015984426655223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123427294426751916942161189 23142617705015984426655223)
  ·
    refine ⟨34713926557523976639982835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23142617705015984426655223 34713926557523976639982835)
    ·
      refine ⟨52070889836285964959974253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34713926557523976639982835 52070889836285964959974253)
      ·
        refine ⟨19526583688607236859990345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52070889836285964959974253 19526583688607236859990345)
        ·
          refine ⟨14644937766455427644992759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19526583688607236859990345 14644937766455427644992759)
          ·
            refine ⟨21967406649683141467489139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14644937766455427644992759 21967406649683141467489139)
            ·
              refine ⟨32951109974524712201233709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21967406649683141467489139 32951109974524712201233709)
              ·
                refine ⟨12356666240446767075462641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32951109974524712201233709 12356666240446767075462641)
                ·
                  refine ⟨9267499680335075306596981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12356666240446767075462641 9267499680335075306596981)
                  ·
                    refine ⟨868828095031413309993467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9267499680335075306596981 868828095031413309993467)
                    ·
                      rfl

theorem cell23_5076110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_5076110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076110 prefixEnd_5076110 := by exact prefixLift 5076110
  have htrace : WordTrace (prefixWord ++ tailWord_5076110) baseStart_5076110 baseEnd_5076110 := by
    simpa [prefixWord, tailWord_5076110, baseEnd_5076110] using wordTrace_append hprefix tailTrace_5076110
  have hstable : (prefixWord ++ tailWord_5076110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076110).length < 2 ^ (prefixWord ++ tailWord_5076110).sum := by decide
  have hdescent : baseEnd_5076110 < baseStart_5076110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076163 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 3]
def baseStart_5076163 : Nat := 118140960795 + 5076163 * 2 ^ 59
def prefixEnd_5076163 : Nat := 4983230072969 + 3 ^ 40 * 5076163 * 2
def baseEnd_5076163 : Nat := 2606511499568928222617657

theorem tailTrace_5076163 : CollatzResearch.WordTrace tailWord_5076163 prefixEnd_5076163 2606511499568928222617657 := by
  unfold tailWord_5076163
  simp only [CollatzResearch.WordTrace]
  refine ⟨185142874708935865464921143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123428583139290576976614095 185142874708935865464921143)
  ·
    refine ⟨277714312063403798197381715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185142874708935865464921143 277714312063403798197381715)
    ·
      refine ⟨416571468095105697296072573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277714312063403798197381715 416571468095105697296072573)
      ·
        refine ⟨156214300535664636486027215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416571468095105697296072573 156214300535664636486027215)
        ·
          refine ⟨234321450803496954729040823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156214300535664636486027215 234321450803496954729040823)
          ·
            refine ⟨351482176205245432093561235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234321450803496954729040823 351482176205245432093561235)
            ·
              refine ⟨527223264307868148140341853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351482176205245432093561235 527223264307868148140341853)
              ·
                refine ⟨197708724115450555552628195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 527223264307868148140341853 197708724115450555552628195)
                ·
                  refine ⟨296563086173175833328942293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197708724115450555552628195 296563086173175833328942293)
                  ·
                    refine ⟨6950697332183808593647085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 296563086173175833328942293 6950697332183808593647085)
                    ·
                      refine ⟨2606511499568928222617657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6950697332183808593647085 2606511499568928222617657)
                      ·
                        rfl

theorem cell23_5076163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_5076163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076163 prefixEnd_5076163 := by exact prefixLift 5076163
  have htrace : WordTrace (prefixWord ++ tailWord_5076163) baseStart_5076163 baseEnd_5076163 := by
    simpa [prefixWord, tailWord_5076163, baseEnd_5076163] using wordTrace_append hprefix tailTrace_5076163
  have hstable : (prefixWord ++ tailWord_5076163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076163).length < 2 ^ (prefixWord ++ tailWord_5076163).sum := by decide
  have hdescent : baseEnd_5076163 < baseStart_5076163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076164 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_5076164 : Nat := 118140960795 + 5076164 * 2 ^ 59
def prefixEnd_5076164 : Nat := 4983230072969 + 3 ^ 40 * 5076164 * 2
def baseEnd_5076164 : Nat := 2606512013049582718705153

theorem tailTrace_5076164 : CollatzResearch.WordTrace tailWord_5076164 prefixEnd_5076164 2606512013049582718705153 := by
  unfold tailWord_5076164
  simp only [CollatzResearch.WordTrace]
  refine ⟨92571455590966121317853773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123428607454621495090471697 92571455590966121317853773)
  ·
    refine ⟨34714295846612295494195165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92571455590966121317853773 34714295846612295494195165)
    ·
      refine ⟨13017860942479610810323187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34714295846612295494195165 13017860942479610810323187)
      ·
        refine ⟨19526791413719416215484781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13017860942479610810323187 19526791413719416215484781)
        ·
          refine ⟨7322546780144781080806793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19526791413719416215484781 7322546780144781080806793)
          ·
            refine ⟨5491910085108585810605095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7322546780144781080806793 5491910085108585810605095)
            ·
              refine ⟨8237865127662878715907643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5491910085108585810605095 8237865127662878715907643)
              ·
                refine ⟨12356797691494318073861465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8237865127662878715907643 12356797691494318073861465)
                ·
                  refine ⟨9267598268620738555396099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12356797691494318073861465 9267598268620738555396099)
                  ·
                    refine ⟨13901397402931107833094149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9267598268620738555396099 13901397402931107833094149)
                    ·
                      refine ⟨2606512013049582718705153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13901397402931107833094149 2606512013049582718705153)
                      ·
                        rfl

theorem cell23_5076164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_5076164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076164 prefixEnd_5076164 := by exact prefixLift 5076164
  have htrace : WordTrace (prefixWord ++ tailWord_5076164) baseStart_5076164 baseEnd_5076164 := by
    simpa [prefixWord, tailWord_5076164, baseEnd_5076164] using wordTrace_append hprefix tailTrace_5076164
  have hstable : (prefixWord ++ tailWord_5076164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076164).length < 2 ^ (prefixWord ++ tailWord_5076164).sum := by decide
  have hdescent : baseEnd_5076164 < baseStart_5076164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076247 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 2, 4]
def baseStart_5076247 : Nat := 118140960795 + 5076247 * 2 ^ 59
def prefixEnd_5076247 : Nat := 4983230072969 + 3 ^ 40 * 5076247 * 2
def baseEnd_5076247 : Nat := 868851543981301964655757

theorem tailTrace_5076247 : CollatzResearch.WordTrace tailWord_5076247 prefixEnd_5076247 868851543981301964655757 := by
  unfold tailWord_5076247
  simp only [CollatzResearch.WordTrace]
  refine ⟨185145938440631547810978995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123430625627087698540652663 185145938440631547810978995)
  ·
    refine ⟨277718907660947321716468493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185145938440631547810978995 277718907660947321716468493)
    ·
      refine ⟨104144590372855245643675685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277718907660947321716468493 104144590372855245643675685)
      ·
        refine ⟨19527110694910358558189191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104144590372855245643675685 19527110694910358558189191)
        ·
          refine ⟨29290666042365537837283787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19527110694910358558189191 29290666042365537837283787)
          ·
            refine ⟨43935999063548306755925681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29290666042365537837283787 43935999063548306755925681)
            ·
              refine ⟨32951999297661230066944261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43935999063548306755925681 32951999297661230066944261)
              ·
                refine ⟨6178499868311480637552049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32951999297661230066944261 6178499868311480637552049)
                ·
                  refine ⟨4633874901233610478164037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6178499868311480637552049 4633874901233610478164037)
                  ·
                    refine ⟨868851543981301964655757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4633874901233610478164037 868851543981301964655757)
                    ·
                      rfl

theorem cell23_5076247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_5076247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076247 prefixEnd_5076247 := by exact prefixLift 5076247
  have htrace : WordTrace (prefixWord ++ tailWord_5076247) baseStart_5076247 baseEnd_5076247 := by
    simpa [prefixWord, tailWord_5076247, baseEnd_5076247] using wordTrace_append hprefix tailTrace_5076247
  have hstable : (prefixWord ++ tailWord_5076247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076247).length < 2 ^ (prefixWord ++ tailWord_5076247).sum := by decide
  have hdescent : baseEnd_5076247 < baseStart_5076247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076250 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_5076250 : Nat := 118140960795 + 5076250 * 2 ^ 59
def prefixEnd_5076250 : Nat := 4983230072969 + 3 ^ 40 * 5076250 * 2
def baseEnd_5076250 : Nat := 2606556172385869382229757

theorem tailTrace_5076250 : CollatzResearch.WordTrace tailWord_5076250 prefixEnd_5076250 2606556172385869382229757 := by
  unfold tailWord_5076250
  simp only [CollatzResearch.WordTrace]
  refine ⟨46286511964905169830834551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123430698573080452882225469 46286511964905169830834551)
  ·
    refine ⟨69429767947357754746251827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46286511964905169830834551 69429767947357754746251827)
    ·
      refine ⟨104144651921036632119377741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69429767947357754746251827 104144651921036632119377741)
      ·
        refine ⟨39054244470388737044766653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104144651921036632119377741 39054244470388737044766653)
        ·
          refine ⟨14645341676395776391787495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39054244470388737044766653 14645341676395776391787495)
          ·
            refine ⟨21968012514593664587681243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14645341676395776391787495 21968012514593664587681243)
            ·
              refine ⟨32952018771890496881521865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21968012514593664587681243 32952018771890496881521865)
              ·
                refine ⟨24714014078917872661141399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32952018771890496881521865 24714014078917872661141399)
                ·
                  refine ⟨37071021118376808991712099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24714014078917872661141399 37071021118376808991712099)
                  ·
                    refine ⟨55606531677565213487568149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37071021118376808991712099 55606531677565213487568149)
                    ·
                      refine ⟨2606556172385869382229757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55606531677565213487568149 2606556172385869382229757)
                      ·
                        rfl

theorem cell23_5076250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_5076250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076250 prefixEnd_5076250 := by exact prefixLift 5076250
  have htrace : WordTrace (prefixWord ++ tailWord_5076250) baseStart_5076250 baseEnd_5076250 := by
    simpa [prefixWord, tailWord_5076250, baseEnd_5076250] using wordTrace_append hprefix tailTrace_5076250
  have hstable : (prefixWord ++ tailWord_5076250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076250).length < 2 ^ (prefixWord ++ tailWord_5076250).sum := by decide
  have hdescent : baseEnd_5076250 < baseStart_5076250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076260 : List Nat := [2, 3, 1, 3, 1, 1, 4, 8]
def baseStart_5076260 : Nat := 118140960795 + 5076260 * 2 ^ 59
def prefixEnd_5076260 : Nat := 4983230072969 + 3 ^ 40 * 5076260 * 2
def baseEnd_5076260 : Nat := 96539307673793123818693

theorem tailTrace_5076260 : CollatzResearch.WordTrace tailWord_5076260 prefixEnd_5076260 96539307673793123818693 := by
  unfold tailWord_5076260
  simp only [CollatzResearch.WordTrace]
  refine ⟨92573206294792225515601117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123430941726389634020801489 92573206294792225515601117)
  ·
    refine ⟨34714952360547084568350419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92573206294792225515601117 34714952360547084568350419)
    ·
      refine ⟨52072428540820626852525629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34714952360547084568350419 52072428540820626852525629)
      ·
        refine ⟨19527160702807735069697111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52072428540820626852525629 19527160702807735069697111)
        ·
          refine ⟨29290741054211602604545667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19527160702807735069697111 29290741054211602604545667)
          ·
            refine ⟨43936111581317403906818501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29290741054211602604545667 43936111581317403906818501)
            ·
              refine ⟨8238020921497013232528469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43936111581317403906818501 8238020921497013232528469)
              ·
                refine ⟨96539307673793123818693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8238020921497013232528469 96539307673793123818693)
                ·
                  rfl

theorem cell23_5076260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 8].length) (baseStart_5076260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076260 prefixEnd_5076260 := by exact prefixLift 5076260
  have htrace : WordTrace (prefixWord ++ tailWord_5076260) baseStart_5076260 baseEnd_5076260 := by
    simpa [prefixWord, tailWord_5076260, baseEnd_5076260] using wordTrace_append hprefix tailTrace_5076260
  have hstable : (prefixWord ++ tailWord_5076260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076260).length < 2 ^ (prefixWord ++ tailWord_5076260).sum := by decide
  have hdescent : baseEnd_5076260 < baseStart_5076260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076264 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 2, 4]
def baseStart_5076264 : Nat := 118140960795 + 5076264 * 2 ^ 59
def prefixEnd_5076264 : Nat := 4983230072969 + 3 ^ 40 * 5076264 * 2
def baseEnd_5076264 : Nat := 868854453705010775818231

theorem tailTrace_5076264 : CollatzResearch.WordTrace tailWord_5076264 prefixEnd_5076264 868854453705010775818231 := by
  unfold tailWord_5076264
  simp only [CollatzResearch.WordTrace]
  refine ⟨92573279240784979857173923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123431038987713306476231897 92573279240784979857173923)
  ·
    refine ⟨138859918861177469785760885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92573279240784979857173923 138859918861177469785760885)
    ·
      refine ⟨13018117393235387792415083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138859918861177469785760885 13018117393235387792415083)
      ·
        refine ⟨19527176089853081688622625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13018117393235387792415083 19527176089853081688622625)
        ·
          refine ⟨14645382067389811266466969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19527176089853081688622625 14645382067389811266466969)
          ·
            refine ⟨10984036550542358449850227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14645382067389811266466969 10984036550542358449850227)
            ·
              refine ⟨16476054825813537674775341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10984036550542358449850227 16476054825813537674775341)
              ·
                refine ⟨6178520559680076628040753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16476054825813537674775341 6178520559680076628040753)
                ·
                  refine ⟨4633890419760057471030565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6178520559680076628040753 4633890419760057471030565)
                  ·
                    refine ⟨868854453705010775818231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4633890419760057471030565 868854453705010775818231)
                    ·
                      rfl

theorem cell23_5076264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_5076264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076264 prefixEnd_5076264 := by exact prefixLift 5076264
  have htrace : WordTrace (prefixWord ++ tailWord_5076264) baseStart_5076264 baseEnd_5076264 := by
    simpa [prefixWord, tailWord_5076264, baseEnd_5076264] using wordTrace_append hprefix tailTrace_5076264
  have hstable : (prefixWord ++ tailWord_5076264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076264).length < 2 ^ (prefixWord ++ tailWord_5076264).sum := by decide
  have hdescent : baseEnd_5076264 < baseStart_5076264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076274 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_5076274 : Nat := 118140960795 + 5076274 * 2 ^ 59
def prefixEnd_5076274 : Nat := 4983230072969 + 3 ^ 40 * 5076274 * 2
def baseEnd_5076274 : Nat := 2606568495921577288329647

theorem tailTrace_5076274 : CollatzResearch.WordTrace tailWord_5076274 prefixEnd_5076274 2606568495921577288329647 := by
  unfold tailWord_5076274
  simp only [CollatzResearch.WordTrace]
  refine ⟨46286730802883432855552969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123431282141022487614807917 46286730802883432855552969)
  ·
    refine ⟨34715048102162574641664727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46286730802883432855552969 34715048102162574641664727)
    ·
      refine ⟨52072572153243861962497091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34715048102162574641664727 52072572153243861962497091)
      ·
        refine ⟨78108858229865792943745637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52072572153243861962497091 78108858229865792943745637)
        ·
          refine ⟨14645410918099836176952307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78108858229865792943745637 14645410918099836176952307)
          ·
            refine ⟨21968116377149754265428461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14645410918099836176952307 21968116377149754265428461)
            ·
              refine ⟨8238043641431157849535673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21968116377149754265428461 8238043641431157849535673)
              ·
                refine ⟨6178532731073368387151755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8238043641431157849535673 6178532731073368387151755)
                ·
                  refine ⟨9267799096610052580727633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6178532731073368387151755 9267799096610052580727633)
                  ·
                    refine ⟨6950849322457539435545725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9267799096610052580727633 6950849322457539435545725)
                    ·
                      refine ⟨2606568495921577288329647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6950849322457539435545725 2606568495921577288329647)
                      ·
                        rfl

theorem cell23_5076274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_5076274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076274 prefixEnd_5076274 := by exact prefixLift 5076274
  have htrace : WordTrace (prefixWord ++ tailWord_5076274) baseStart_5076274 baseEnd_5076274 := by
    simpa [prefixWord, tailWord_5076274, baseEnd_5076274] using wordTrace_append hprefix tailTrace_5076274
  have hstable : (prefixWord ++ tailWord_5076274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076274).length < 2 ^ (prefixWord ++ tailWord_5076274).sum := by decide
  have hdescent : baseEnd_5076274 < baseStart_5076274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076283 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7]
def baseStart_5076283 : Nat := 118140960795 + 5076283 * 2 ^ 59
def prefixEnd_5076283 : Nat := 4983230072969 + 3 ^ 40 * 5076283 * 2
def baseEnd_5076283 : Nat := 2606573117247467753117105

theorem tailTrace_5076283 : CollatzResearch.WordTrace tailWord_5076283 prefixEnd_5076283 2606573117247467753117105 := by
  unfold tailWord_5076283
  simp only [CollatzResearch.WordTrace]
  refine ⟨185147251468501125959289503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123431500979000750639526335 185147251468501125959289503)
  ·
    refine ⟨277720877202751688938934255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185147251468501125959289503 277720877202751688938934255)
    ·
      refine ⟨416581315804127533408401383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277720877202751688938934255 416581315804127533408401383)
      ·
        refine ⟨624871973706191300112602075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416581315804127533408401383 624871973706191300112602075)
        ·
          refine ⟨937307960559286950168903113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624871973706191300112602075 937307960559286950168903113)
          ·
            refine ⟨702980970419465212626677335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 937307960559286950168903113 702980970419465212626677335)
            ·
              refine ⟨1054471455629197818940016003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702980970419465212626677335 1054471455629197818940016003)
              ·
                refine ⟨1581707183443796728410024005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054471455629197818940016003 1581707183443796728410024005)
                ·
                  refine ⟨296570096895711886576879501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581707183443796728410024005 296570096895711886576879501)
                  ·
                    refine ⟨111213786335891957466329813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296570096895711886576879501 111213786335891957466329813)
                    ·
                      refine ⟨2606573117247467753117105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111213786335891957466329813 2606573117247467753117105)
                      ·
                        rfl

theorem cell23_5076283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_5076283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076283 prefixEnd_5076283 := by exact prefixLift 5076283
  have htrace : WordTrace (prefixWord ++ tailWord_5076283) baseStart_5076283 baseEnd_5076283 := by
    simpa [prefixWord, tailWord_5076283, baseEnd_5076283] using wordTrace_append hprefix tailTrace_5076283
  have hstable : (prefixWord ++ tailWord_5076283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076283).length < 2 ^ (prefixWord ++ tailWord_5076283).sum := by decide
  have hdescent : baseEnd_5076283 < baseStart_5076283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076287 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 3]
def baseStart_5076287 : Nat := 118140960795 + 5076287 * 2 ^ 59
def prefixEnd_5076287 : Nat := 4983230072969 + 3 ^ 40 * 5076287 * 2
def baseEnd_5076287 : Nat := 2606575171170085737467087

theorem tailTrace_5076287 : CollatzResearch.WordTrace tailWord_5076287 prefixEnd_5076287 2606575171170085737467087 := by
  unfold tailWord_5076287
  simp only [CollatzResearch.WordTrace]
  refine ⟨185147397360486634642435115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123431598240324423094956743 185147397360486634642435115)
  ·
    refine ⟨277721096040729951963652673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185147397360486634642435115 277721096040729951963652673)
    ·
      refine ⟨208290822030547463972739505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277721096040729951963652673 208290822030547463972739505)
      ·
        refine ⟨156218116522910597979554629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208290822030547463972739505 156218116522910597979554629)
        ·
          refine ⟨29290896848045737121166493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156218116522910597979554629 29290896848045737121166493)
          ·
            refine ⟨10984086318017151420437435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29290896848045737121166493 10984086318017151420437435)
            ·
              refine ⟨16476129477025727130656153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10984086318017151420437435 16476129477025727130656153)
              ·
                refine ⟨12357097107769295347992115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16476129477025727130656153 12357097107769295347992115)
                ·
                  refine ⟨18535645661653943021988173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12357097107769295347992115 18535645661653943021988173)
                  ·
                    refine ⟨6950867123120228633245565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18535645661653943021988173 6950867123120228633245565)
                    ·
                      refine ⟨2606575171170085737467087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6950867123120228633245565 2606575171170085737467087)
                      ·
                        rfl

theorem cell23_5076287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_5076287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076287 prefixEnd_5076287 := by exact prefixLift 5076287
  have htrace : WordTrace (prefixWord ++ tailWord_5076287) baseStart_5076287 baseEnd_5076287 := by
    simpa [prefixWord, tailWord_5076287, baseEnd_5076287] using wordTrace_append hprefix tailTrace_5076287
  have hstable : (prefixWord ++ tailWord_5076287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076287).length < 2 ^ (prefixWord ++ tailWord_5076287).sum := by decide
  have hdescent : baseEnd_5076287 < baseStart_5076287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076294 : List Nat := [6, 1, 1, 3, 1, 11]
def baseStart_5076294 : Nat := 118140960795 + 5076294 * 2 ^ 59
def prefixEnd_5076294 : Nat := 4983230072969 + 3 ^ 40 * 5076294 * 2
def baseEnd_5076294 : Nat := 10726661586562416502385

theorem tailTrace_5076294 : CollatzResearch.WordTrace tailWord_5076294 prefixEnd_5076294 10726661586562416502385 := by
  unfold tailWord_5076294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5785864145983164838685623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123431768447640849891959957 5785864145983164838685623)
  ·
    refine ⟨8678796218974747258028435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5785864145983164838685623 8678796218974747258028435)
    ·
      refine ⟨13018194328462120887042653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8678796218974747258028435 13018194328462120887042653)
      ·
        refine ⟨4881822873173295332640995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13018194328462120887042653 4881822873173295332640995)
        ·
          refine ⟨7322734309759942998961493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881822873173295332640995 7322734309759942998961493)
          ·
            refine ⟨10726661586562416502385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7322734309759942998961493 10726661586562416502385)
            ·
              rfl

theorem cell23_5076294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 11].length) (baseStart_5076294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076294 prefixEnd_5076294 := by exact prefixLift 5076294
  have htrace : WordTrace (prefixWord ++ tailWord_5076294) baseStart_5076294 baseEnd_5076294 := by
    simpa [prefixWord, tailWord_5076294, baseEnd_5076294] using wordTrace_append hprefix tailTrace_5076294
  have hstable : (prefixWord ++ tailWord_5076294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076294).length < 2 ^ (prefixWord ++ tailWord_5076294).sum := by decide
  have hdescent : baseEnd_5076294 < baseStart_5076294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076304 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 2, 1, 3]
def baseStart_5076304 : Nat := 118140960795 + 5076304 * 2 ^ 59
def prefixEnd_5076304 : Nat := 4983230072969 + 3 ^ 40 * 5076304 * 2
def baseEnd_5076304 : Nat := 2606583900341212170954509

theorem tailTrace_5076304 : CollatzResearch.WordTrace tailWord_5076304 prefixEnd_5076304 2606583900341212170954509 := by
  unfold tailWord_5076304
  simp only [CollatzResearch.WordTrace]
  refine ⟨92574008700712523272901983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123432011600950031030535977 92574008700712523272901983)
  ·
    refine ⟨138861013051068784909352975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92574008700712523272901983 138861013051068784909352975)
    ·
      refine ⟨208291519576603177364029463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138861013051068784909352975 208291519576603177364029463)
      ·
        refine ⟨312437279364904766046044195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208291519576603177364029463 312437279364904766046044195)
        ·
          refine ⟨468655919047357149069066293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312437279364904766046044195 468655919047357149069066293)
          ·
            refine ⟨43936492410689732725224965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 468655919047357149069066293 43936492410689732725224965)
            ·
              refine ⟨8238092327004324885979681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43936492410689732725224965 8238092327004324885979681)
              ·
                refine ⟨6178569245253243664484761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8238092327004324885979681 6178569245253243664484761)
                ·
                  refine ⟨4633926933939932748363571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6178569245253243664484761 4633926933939932748363571)
                  ·
                    refine ⟨6950890400909899122545357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4633926933939932748363571 6950890400909899122545357)
                    ·
                      refine ⟨2606583900341212170954509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6950890400909899122545357 2606583900341212170954509)
                      ·
                        rfl

theorem cell23_5076304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 1, 3].length) (baseStart_5076304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076304 prefixEnd_5076304 := by exact prefixLift 5076304
  have htrace : WordTrace (prefixWord ++ tailWord_5076304) baseStart_5076304 baseEnd_5076304 := by
    simpa [prefixWord, tailWord_5076304, baseEnd_5076304] using wordTrace_append hprefix tailTrace_5076304
  have hstable : (prefixWord ++ tailWord_5076304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076304).length < 2 ^ (prefixWord ++ tailWord_5076304).sum := by decide
  have hdescent : baseEnd_5076304 < baseStart_5076304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076320 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 1, 8]
def baseStart_5076320 : Nat := 118140960795 + 5076320 * 2 ^ 59
def prefixEnd_5076320 : Nat := 4983230072969 + 3 ^ 40 * 5076320 * 2
def baseEnd_5076320 : Nat := 868864038677228036118145

theorem tailTrace_5076320 : CollatzResearch.WordTrace tailWord_5076320 prefixEnd_5076320 868864038677228036118145 := by
  unfold tailWord_5076320
  simp only [CollatzResearch.WordTrace]
  refine ⟨92574300484683540639193207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123432400646244720852257609 92574300484683540639193207)
  ·
    refine ⟨138861450727025310958789811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92574300484683540639193207 138861450727025310958789811)
    ·
      refine ⟨208292176090537966438184717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138861450727025310958789811 208292176090537966438184717)
      ·
        refine ⟨78109566033951737414319269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208292176090537966438184717 78109566033951737414319269)
        ·
          refine ⟨14645543631365950765184863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78109566033951737414319269 14645543631365950765184863)
          ·
            refine ⟨21968315447048926147777295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14645543631365950765184863 21968315447048926147777295)
            ·
              refine ⟨32952473170573389221665943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21968315447048926147777295 32952473170573389221665943)
              ·
                refine ⟨49428709755860083832498915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32952473170573389221665943 49428709755860083832498915)
                ·
                  refine ⟨74143064633790125748748373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49428709755860083832498915 74143064633790125748748373)
                  ·
                    refine ⟨868864038677228036118145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74143064633790125748748373 868864038677228036118145)
                    ·
                      rfl

theorem cell23_5076320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_5076320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076320 prefixEnd_5076320 := by exact prefixLift 5076320
  have htrace : WordTrace (prefixWord ++ tailWord_5076320) baseStart_5076320 baseEnd_5076320 := by
    simpa [prefixWord, tailWord_5076320, baseEnd_5076320] using wordTrace_append hprefix tailTrace_5076320
  have hstable : (prefixWord ++ tailWord_5076320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076320).length < 2 ^ (prefixWord ++ tailWord_5076320).sum := by decide
  have hdescent : baseEnd_5076320 < baseStart_5076320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076354 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5076354 : Nat := 118140960795 + 5076354 * 2 ^ 59
def prefixEnd_5076354 : Nat := 4983230072969 + 3 ^ 40 * 5076354 * 2
def baseEnd_5076354 : Nat := 868869858124645658443093

theorem tailTrace_5076354 : CollatzResearch.WordTrace tailWord_5076354 prefixEnd_5076354 868869858124645658443093 := by
  unfold tailWord_5076354
  simp only [CollatzResearch.WordTrace]
  refine ⟨46287460262810976271281029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123433227367495936723416077 46287460262810976271281029)
  ·
    refine ⟨8678898799277058050865193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46287460262810976271281029 8678898799277058050865193)
    ·
      refine ⟨6509174099457793538148895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8678898799277058050865193 6509174099457793538148895)
      ·
        refine ⟨9763761149186690307223343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6509174099457793538148895 9763761149186690307223343)
        ·
          refine ⟨14645641723780035460835015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9763761149186690307223343 14645641723780035460835015)
          ·
            refine ⟨21968462585670053191252523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14645641723780035460835015 21968462585670053191252523)
            ·
              refine ⟨32952693878505079786878785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21968462585670053191252523 32952693878505079786878785)
              ·
                refine ⟨24714520408878809840159089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32952693878505079786878785 24714520408878809840159089)
                ·
                  refine ⟨18535890306659107380119317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24714520408878809840159089 18535890306659107380119317)
                  ·
                    refine ⟨868869858124645658443093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18535890306659107380119317 868869858124645658443093)
                    ·
                      rfl

theorem cell23_5076354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5076354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076354 prefixEnd_5076354 := by exact prefixLift 5076354
  have htrace : WordTrace (prefixWord ++ tailWord_5076354) baseStart_5076354 baseEnd_5076354 := by
    simpa [prefixWord, tailWord_5076354, baseEnd_5076354] using wordTrace_append hprefix tailTrace_5076354
  have hstable : (prefixWord ++ tailWord_5076354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076354).length < 2 ^ (prefixWord ++ tailWord_5076354).sum := by decide
  have hdescent : baseEnd_5076354 < baseStart_5076354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076361 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 4, 2, 2]
def baseStart_5076361 : Nat := 118140960795 + 5076361 * 2 ^ 59
def prefixEnd_5076361 : Nat := 4983230072969 + 3 ^ 40 * 5076361 * 2
def baseEnd_5076361 : Nat := 2606613168738518447941747

theorem tailTrace_5076361 : CollatzResearch.WordTrace tailWord_5076361 prefixEnd_5076361 2606613168738518447941747 := by
  unfold tailWord_5076361
  simp only [CollatzResearch.WordTrace]
  refine ⟨185150096362218545280628937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123433397574812363520419291 185150096362218545280628937)
  ·
    refine ⟨138862572271663908960471703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185150096362218545280628937 138862572271663908960471703)
    ·
      refine ⟨208293858407495863440707555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138862572271663908960471703 208293858407495863440707555)
      ·
        refine ⟨312440787611243795161061333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208293858407495863440707555 312440787611243795161061333)
        ·
          refine ⟨7322830959638526449087375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 312440787611243795161061333 7322830959638526449087375)
          ·
            refine ⟨10984246439457789673631063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322830959638526449087375 10984246439457789673631063)
            ·
              refine ⟨16476369659186684510446595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10984246439457789673631063 16476369659186684510446595)
              ·
                refine ⟨24714554488780026765669893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16476369659186684510446595 24714554488780026765669893)
                ·
                  refine ⟨4633978966646255018563105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24714554488780026765669893 4633978966646255018563105)
                  ·
                    refine ⟨3475484224984691263922329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633978966646255018563105 3475484224984691263922329)
                    ·
                      refine ⟨2606613168738518447941747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475484224984691263922329 2606613168738518447941747)
                      ·
                        rfl

theorem cell23_5076361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 2, 2].length) (baseStart_5076361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076361 prefixEnd_5076361 := by exact prefixLift 5076361
  have htrace : WordTrace (prefixWord ++ tailWord_5076361) baseStart_5076361 baseEnd_5076361 := by
    simpa [prefixWord, tailWord_5076361, baseEnd_5076361] using wordTrace_append hprefix tailTrace_5076361
  have hstable : (prefixWord ++ tailWord_5076361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076361).length < 2 ^ (prefixWord ++ tailWord_5076361).sum := by decide
  have hdescent : baseEnd_5076361 < baseStart_5076361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076377 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 3]
def baseStart_5076377 : Nat := 118140960795 + 5076377 * 2 ^ 59
def prefixEnd_5076377 : Nat := 4983230072969 + 3 ^ 40 * 5076377 * 2
def baseEnd_5076377 : Nat := 2606621384428990385341673

theorem tailTrace_5076377 : CollatzResearch.WordTrace tailWord_5076377 prefixEnd_5076377 2606621384428990385341673 := by
  unfold tailWord_5076377
  simp only [CollatzResearch.WordTrace]
  refine ⟨185150679930160580013211385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123433786620107053342140923 185150679930160580013211385)
  ·
    refine ⟨138863009947620435009908539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185150679930160580013211385 138863009947620435009908539)
    ·
      refine ⟨208294514921430652514862809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138863009947620435009908539 208294514921430652514862809)
      ·
        refine ⟨156220886191072989386147107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208294514921430652514862809 156220886191072989386147107)
        ·
          refine ⟨234331329286609484079220661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156220886191072989386147107 234331329286609484079220661)
          ·
            refine ⟨21968562120619639132426937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234331329286609484079220661 21968562120619639132426937)
            ·
              refine ⟨16476421590464729349320203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21968562120619639132426937 16476421590464729349320203)
              ·
                refine ⟨24714632385697094023980305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16476421590464729349320203 24714632385697094023980305)
                ·
                  refine ⟨18535974289272820517985229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24714632385697094023980305 18535974289272820517985229)
                  ·
                    refine ⟨6950990358477307694244461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18535974289272820517985229 6950990358477307694244461)
                    ·
                      refine ⟨2606621384428990385341673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6950990358477307694244461 2606621384428990385341673)
                      ·
                        rfl

theorem cell23_5076377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_5076377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076377 prefixEnd_5076377 := by exact prefixLift 5076377
  have htrace : WordTrace (prefixWord ++ tailWord_5076377) baseStart_5076377 baseEnd_5076377 := by
    simpa [prefixWord, tailWord_5076377, baseEnd_5076377] using wordTrace_append hprefix tailTrace_5076377
  have hstable : (prefixWord ++ tailWord_5076377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076377).length < 2 ^ (prefixWord ++ tailWord_5076377).sum := by decide
  have hdescent : baseEnd_5076377 < baseStart_5076377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076378 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2]
def baseStart_5076378 : Nat := 118140960795 + 5076378 * 2 ^ 59
def prefixEnd_5076378 : Nat := 4983230072969 + 3 ^ 40 * 5076378 * 2
def baseEnd_5076378 : Nat := 2606621897909644881429169

theorem tailTrace_5076378 : CollatzResearch.WordTrace tailWord_5076378 prefixEnd_5076378 2606621897909644881429169 := by
  unfold tailWord_5076378
  simp only [CollatzResearch.WordTrace]
  refine ⟨46287679100789239295999447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123433810935437971455998525 46287679100789239295999447)
  ·
    refine ⟨69431518651183858943999171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46287679100789239295999447 69431518651183858943999171)
    ·
      refine ⟨104147277976775788415998757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69431518651183858943999171 104147277976775788415998757)
      ·
        refine ⟨19527614620645460327999767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104147277976775788415998757 19527614620645460327999767)
        ·
          refine ⟨29291421930968190491999651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19527614620645460327999767 29291421930968190491999651)
          ·
            refine ⟨43937132896452285737999477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29291421930968190491999651 43937132896452285737999477)
            ·
              refine ⟨4119106209042401787937451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43937132896452285737999477 4119106209042401787937451)
              ·
                refine ⟨6178659313563602681906177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119106209042401787937451 6178659313563602681906177)
                ·
                  refine ⟨4633994485172702011429633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6178659313563602681906177 4633994485172702011429633)
                  ·
                    refine ⟨3475495863879526508572225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633994485172702011429633 3475495863879526508572225)
                    ·
                      refine ⟨2606621897909644881429169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475495863879526508572225 2606621897909644881429169)
                      ·
                        rfl

theorem cell23_5076378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_5076378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076378 prefixEnd_5076378 := by exact prefixLift 5076378
  have htrace : WordTrace (prefixWord ++ tailWord_5076378) baseStart_5076378 baseEnd_5076378 := by
    simpa [prefixWord, tailWord_5076378, baseEnd_5076378] using wordTrace_append hprefix tailTrace_5076378
  have hstable : (prefixWord ++ tailWord_5076378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076378).length < 2 ^ (prefixWord ++ tailWord_5076378).sum := by decide
  have hdescent : baseEnd_5076378 < baseStart_5076378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076501 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_5076501 : Nat := 118140960795 + 5076501 * 2 ^ 59
def prefixEnd_5076501 : Nat := 4983230072969 + 3 ^ 40 * 5076501 * 2
def baseEnd_5076501 : Nat := 2606685056030147900191103

theorem tailTrace_5076501 : CollatzResearch.WordTrace tailWord_5076501 prefixEnd_5076501 2606685056030147900191103 := by
  unfold tailWord_5076501
  simp only [CollatzResearch.WordTrace]
  refine ⟨185155202581711349190725357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123436801721140899460483571 185155202581711349190725357)
  ·
    refine ⟨69433200968141755946522009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185155202581711349190725357 69433200968141755946522009)
    ·
      refine ⟨52074900726106316959891507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69433200968141755946522009 52074900726106316959891507)
      ·
        refine ⟨78112351089159475439837261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52074900726106316959891507 78112351089159475439837261)
        ·
          refine ⟨29292131658434803289938973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78112351089159475439837261 29292131658434803289938973)
          ·
            refine ⟨10984549371913051233727115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29292131658434803289938973 10984549371913051233727115)
            ·
              refine ⟨16476824057869576850590673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10984549371913051233727115 16476824057869576850590673)
              ·
                refine ⟨12357618043402182637943005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16476824057869576850590673 12357618043402182637943005)
                ·
                  refine ⟨4634106766275818489228627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12357618043402182637943005 4634106766275818489228627)
                  ·
                    refine ⟨6951160149413727733842941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4634106766275818489228627 6951160149413727733842941)
                    ·
                      refine ⟨2606685056030147900191103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951160149413727733842941 2606685056030147900191103)
                      ·
                        rfl

theorem cell23_5076501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_5076501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076501 prefixEnd_5076501 := by exact prefixLift 5076501
  have htrace : WordTrace (prefixWord ++ tailWord_5076501) baseStart_5076501 baseEnd_5076501 := by
    simpa [prefixWord, tailWord_5076501, baseEnd_5076501] using wordTrace_append hprefix tailTrace_5076501
  have hstable : (prefixWord ++ tailWord_5076501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076501).length < 2 ^ (prefixWord ++ tailWord_5076501).sum := by decide
  have hdescent : baseEnd_5076501 < baseStart_5076501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076511 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 2, 3, 2]
def baseStart_5076511 : Nat := 118140960795 + 5076511 * 2 ^ 59
def prefixEnd_5076511 : Nat := 4983230072969 + 3 ^ 40 * 5076511 * 2
def baseEnd_5076511 : Nat := 2606690190836692861066057

theorem tailTrace_5076511 : CollatzResearch.WordTrace tailWord_5076511 prefixEnd_5076511 2606690190836692861066057 := by
  unfold tailWord_5076511
  simp only [CollatzResearch.WordTrace]
  refine ⟨185155567311675120898589387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123437044874450080599059591 185155567311675120898589387)
  ·
    refine ⟨277733350967512681347884081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185155567311675120898589387 277733350967512681347884081)
    ·
      refine ⟨208300013225634511010913061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277733350967512681347884081 208300013225634511010913061)
      ·
        refine ⟨39056252479806470814546199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208300013225634511010913061 39056252479806470814546199)
        ·
          refine ⟨58584378719709706221819299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39056252479806470814546199 58584378719709706221819299)
          ·
            refine ⟨87876568079564559332728949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58584378719709706221819299 87876568079564559332728949)
            ·
              refine ⟨8238428257459177437443339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87876568079564559332728949 8238428257459177437443339)
              ·
                refine ⟨12357642386188766156165009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8238428257459177437443339 12357642386188766156165009)
                ·
                  refine ⟨9268231789641574617123757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12357642386188766156165009 9268231789641574617123757)
                  ·
                    refine ⟨3475586921115590481421409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9268231789641574617123757 3475586921115590481421409)
                    ·
                      refine ⟨2606690190836692861066057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475586921115590481421409 2606690190836692861066057)
                      ·
                        rfl

theorem cell23_5076511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_5076511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076511 prefixEnd_5076511 := by exact prefixLift 5076511
  have htrace : WordTrace (prefixWord ++ tailWord_5076511) baseStart_5076511 baseEnd_5076511 := by
    simpa [prefixWord, tailWord_5076511, baseEnd_5076511] using wordTrace_append hprefix tailTrace_5076511
  have hstable : (prefixWord ++ tailWord_5076511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076511).length < 2 ^ (prefixWord ++ tailWord_5076511).sum := by decide
  have hdescent : baseEnd_5076511 < baseStart_5076511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076551 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 1, 6]
def baseStart_5076551 : Nat := 118140960795 + 5076551 * 2 ^ 59
def prefixEnd_5076551 : Nat := 4983230072969 + 3 ^ 40 * 5076551 * 2
def baseEnd_5076551 : Nat := 868903576687624234855291

theorem tailTrace_5076551 : CollatzResearch.WordTrace tailWord_5076551 prefixEnd_5076551 868903576687624234855291 := by
  unfold tailWord_5076551
  simp only [CollatzResearch.WordTrace]
  refine ⟨185157026231530207730045507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123438017487686805153363671 185157026231530207730045507)
  ·
    refine ⟨277735539347295311595068261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185157026231530207730045507 277735539347295311595068261)
    ·
      refine ⟨52075413627617870924075299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277735539347295311595068261 52075413627617870924075299)
      ·
        refine ⟨78113120441426806386112949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52075413627617870924075299 78113120441426806386112949)
        ·
          refine ⟨7323105041383763098698089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78113120441426806386112949 7323105041383763098698089)
          ·
            refine ⟨5492328781037822324023567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7323105041383763098698089 5492328781037822324023567)
            ·
              refine ⟨8238493171556733486035351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5492328781037822324023567 8238493171556733486035351)
              ·
                refine ⟨12357739757335100229053027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8238493171556733486035351 12357739757335100229053027)
                ·
                  refine ⟨18536609636002650343579541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12357739757335100229053027 18536609636002650343579541)
                  ·
                    refine ⟨868903576687624234855291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18536609636002650343579541 868903576687624234855291)
                    ·
                      rfl

theorem cell23_5076551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_5076551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076551 prefixEnd_5076551 := by exact prefixLift 5076551
  have htrace : WordTrace (prefixWord ++ tailWord_5076551) baseStart_5076551 baseEnd_5076551 := by
    simpa [prefixWord, tailWord_5076551, baseEnd_5076551] using wordTrace_append hprefix tailTrace_5076551
  have hstable : (prefixWord ++ tailWord_5076551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076551).length < 2 ^ (prefixWord ++ tailWord_5076551).sum := by decide
  have hdescent : baseEnd_5076551 < baseStart_5076551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076561 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_5076561 : Nat := 118140960795 + 5076561 * 2 ^ 59
def prefixEnd_5076561 : Nat := 4983230072969 + 3 ^ 40 * 5076561 * 2
def baseEnd_5076561 : Nat := 2606715864869417665440827

theorem tailTrace_5076561 : CollatzResearch.WordTrace tailWord_5076561 prefixEnd_5076561 2606715864869417665440827 := by
  unfold tailWord_5076561
  simp only [CollatzResearch.WordTrace]
  refine ⟨185157390961493979437909537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123438260640995986291939691 185157390961493979437909537)
  ·
    refine ⟨138868043221120484578432153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185157390961493979437909537 138868043221120484578432153)
    ·
      refine ⟨104151032415840363433824115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138868043221120484578432153 104151032415840363433824115)
      ·
        refine ⟨156226548623760545150736173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104151032415840363433824115 156226548623760545150736173)
        ·
          refine ⟨58584955733910204431526065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156226548623760545150736173 58584955733910204431526065)
          ·
            refine ⟨43938716800432653323644549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58584955733910204431526065 43938716800432653323644549)
            ·
              refine ⟨8238509400081122498183353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43938716800432653323644549 8238509400081122498183353)
              ·
                refine ⟨6178882050060841873637515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8238509400081122498183353 6178882050060841873637515)
                ·
                  refine ⟨9268323075091262810456273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6178882050060841873637515 9268323075091262810456273)
                  ·
                    refine ⟨6951242306318447107842205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9268323075091262810456273 6951242306318447107842205)
                    ·
                      refine ⟨2606715864869417665440827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951242306318447107842205 2606715864869417665440827)
                      ·
                        rfl

theorem cell23_5076561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_5076561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076561 prefixEnd_5076561 := by exact prefixLift 5076561
  have htrace : WordTrace (prefixWord ++ tailWord_5076561) baseStart_5076561 baseEnd_5076561 := by
    simpa [prefixWord, tailWord_5076561, baseEnd_5076561] using wordTrace_append hprefix tailTrace_5076561
  have hstable : (prefixWord ++ tailWord_5076561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076561).length < 2 ^ (prefixWord ++ tailWord_5076561).sum := by decide
  have hdescent : baseEnd_5076561 < baseStart_5076561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076591 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 3]
def baseStart_5076591 : Nat := 118140960795 + 5076591 * 2 ^ 59
def prefixEnd_5076591 : Nat := 4983230072969 + 3 ^ 40 * 5076591 * 2
def baseEnd_5076591 : Nat := 2606731269289052548065689

theorem tailTrace_5076591 : CollatzResearch.WordTrace tailWord_5076591 prefixEnd_5076591 2606731269289052548065689 := by
  unfold tailWord_5076591
  simp only [CollatzResearch.WordTrace]
  refine ⟨185158485151385294561501627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123438990100923529707667751 185158485151385294561501627)
  ·
    refine ⟨277737727727077941842252441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185158485151385294561501627 277737727727077941842252441)
    ·
      refine ⟨208303295795308456381689331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277737727727077941842252441 208303295795308456381689331)
      ·
        refine ⟨312454943692962684572533997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208303295795308456381689331 312454943692962684572533997)
        ·
          refine ⟨117170603884861006714700249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312454943692962684572533997 117170603884861006714700249)
          ·
            refine ⟨87877952913645755036025187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117170603884861006714700249 87877952913645755036025187)
            ·
              refine ⟨131816929370468632554037781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87877952913645755036025187 131816929370468632554037781)
              ·
                refine ⟨6178918564240717150970521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131816929370468632554037781 6178918564240717150970521)
                ·
                  refine ⟨4634188923180537863227891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6178918564240717150970521 4634188923180537863227891)
                  ·
                    refine ⟨6951283384770806794841837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4634188923180537863227891 6951283384770806794841837)
                    ·
                      refine ⟨2606731269289052548065689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951283384770806794841837 2606731269289052548065689)
                      ·
                        rfl

theorem cell23_5076591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 3].length) (baseStart_5076591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076591 prefixEnd_5076591 := by exact prefixLift 5076591
  have htrace : WordTrace (prefixWord ++ tailWord_5076591) baseStart_5076591 baseEnd_5076591 := by
    simpa [prefixWord, tailWord_5076591, baseEnd_5076591] using wordTrace_append hprefix tailTrace_5076591
  have hstable : (prefixWord ++ tailWord_5076591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076591).length < 2 ^ (prefixWord ++ tailWord_5076591).sum := by decide
  have hdescent : baseEnd_5076591 < baseStart_5076591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076592 : List Nat := [2, 1, 1, 1, 6, 2, 3, 2, 1, 2, 2]
def baseStart_5076592 : Nat := 118140960795 + 5076592 * 2 ^ 59
def prefixEnd_5076592 : Nat := 4983230072969 + 3 ^ 40 * 5076592 * 2
def baseEnd_5076592 : Nat := 2606731782769707044153185

theorem tailTrace_5076592 : CollatzResearch.WordTrace tailWord_5076592 prefixEnd_5076592 2606731782769707044153185 := by
  unfold tailWord_5076592
  simp only [CollatzResearch.WordTrace]
  refine ⟨92579260812190835866144015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123439014416254447821525353 92579260812190835866144015)
  ·
    refine ⟨138868891218286253799216023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92579260812190835866144015 138868891218286253799216023)
    ·
      refine ⟨208303336827429380698824035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138868891218286253799216023 208303336827429380698824035)
      ·
        refine ⟨312455005241144071048236053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208303336827429380698824035 312455005241144071048236053)
        ·
          refine ⟨14646328370678628330386065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 312455005241144071048236053 14646328370678628330386065)
          ·
            refine ⟨10984746278008971247789549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14646328370678628330386065 10984746278008971247789549)
            ·
              refine ⟨4119279854253364217921081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10984746278008971247789549 4119279854253364217921081)
              ·
                refine ⟨3089459890690023163440811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4119279854253364217921081 3089459890690023163440811)
                ·
                  refine ⟨4634189836035034745161217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089459890690023163440811 4634189836035034745161217)
                  ·
                    refine ⟨3475642377026276058870913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4634189836035034745161217 3475642377026276058870913)
                    ·
                      refine ⟨2606731782769707044153185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475642377026276058870913 2606731782769707044153185)
                      ·
                        rfl

theorem cell23_5076592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 2, 2].length) (baseStart_5076592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076592 prefixEnd_5076592 := by exact prefixLift 5076592
  have htrace : WordTrace (prefixWord ++ tailWord_5076592) baseStart_5076592 baseEnd_5076592 := by
    simpa [prefixWord, tailWord_5076592, baseEnd_5076592] using wordTrace_append hprefix tailTrace_5076592
  have hstable : (prefixWord ++ tailWord_5076592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076592).length < 2 ^ (prefixWord ++ tailWord_5076592).sum := by decide
  have hdescent : baseEnd_5076592 < baseStart_5076592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076601 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 3, 3, 2]
def baseStart_5076601 : Nat := 118140960795 + 5076601 * 2 ^ 59
def prefixEnd_5076601 : Nat := 4983230072969 + 3 ^ 40 * 5076601 * 2
def baseEnd_5076601 : Nat := 2606736404095597508940643

theorem tailTrace_5076601 : CollatzResearch.WordTrace tailWord_5076601 prefixEnd_5076601 2606736404095597508940643 := by
  unfold tailWord_5076601
  simp only [CollatzResearch.WordTrace]
  refine ⟨185158849881349066269365657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123439233254232710846243771 185158849881349066269365657)
  ·
    refine ⟨138869137411011799702024243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185158849881349066269365657 138869137411011799702024243)
    ·
      refine ⟨208303706116517699553036365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138869137411011799702024243 208303706116517699553036365)
      ·
        refine ⟨78113889793694137332388637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208303706116517699553036365 78113889793694137332388637)
        ·
          refine ⟨29292708672635301499645739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78113889793694137332388637 29292708672635301499645739)
          ·
            refine ⟨43939063008952952249468609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29292708672635301499645739 43939063008952952249468609)
            ·
              refine ⟨32954297256714714187101457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43939063008952952249468609 32954297256714714187101457)
              ·
                refine ⟨24715722942536035640326093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32954297256714714187101457 24715722942536035640326093)
                ·
                  refine ⟨9268396103451013365122285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24715722942536035640326093 9268396103451013365122285)
                  ·
                    refine ⟨3475648538794130011920857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9268396103451013365122285 3475648538794130011920857)
                    ·
                      refine ⟨2606736404095597508940643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475648538794130011920857 2606736404095597508940643)
                      ·
                        rfl

theorem cell23_5076601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_5076601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076601 prefixEnd_5076601 := by exact prefixLift 5076601
  have htrace : WordTrace (prefixWord ++ tailWord_5076601) baseStart_5076601 baseEnd_5076601 := by
    simpa [prefixWord, tailWord_5076601, baseEnd_5076601] using wordTrace_append hprefix tailTrace_5076601
  have hstable : (prefixWord ++ tailWord_5076601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076601).length < 2 ^ (prefixWord ++ tailWord_5076601).sum := by decide
  have hdescent : baseEnd_5076601 < baseStart_5076601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076607 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 6, 6]
def baseStart_5076607 : Nat := 118140960795 + 5076607 * 2 ^ 59
def prefixEnd_5076607 : Nat := 4983230072969 + 3 ^ 40 * 5076607 * 2
def baseEnd_5076607 : Nat := 868913161659841495155205

theorem tailTrace_5076607 : CollatzResearch.WordTrace tailWord_5076607 prefixEnd_5076607 868913161659841495155205 := by
  unfold tailWord_5076607
  simp only [CollatzResearch.WordTrace]
  refine ⟨185159068719327329294084075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123439379146218219529389383 185159068719327329294084075)
  ·
    refine ⟨277738603078990993941126113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185159068719327329294084075 277738603078990993941126113)
    ·
      refine ⟨208303952309243245455844585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277738603078990993941126113 208303952309243245455844585)
      ·
        refine ⟨156227964231932434091883439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208303952309243245455844585 156227964231932434091883439)
        ·
          refine ⟨234341946347898651137825159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156227964231932434091883439 234341946347898651137825159)
          ·
            refine ⟨351512919521847976706737739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234341946347898651137825159 351512919521847976706737739)
            ·
              refine ⟨527269379282771965060106609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351512919521847976706737739 527269379282771965060106609)
              ·
                refine ⟨395452034462078973795079957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527269379282771965060106609 395452034462078973795079957)
                ·
                  refine ⟨18536814115409951896644373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 395452034462078973795079957 18536814115409951896644373)
                  ·
                    refine ⟨868913161659841495155205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18536814115409951896644373 868913161659841495155205)
                    ·
                      rfl

theorem cell23_5076607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_5076607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076607 prefixEnd_5076607 := by exact prefixLift 5076607
  have htrace : WordTrace (prefixWord ++ tailWord_5076607) baseStart_5076607 baseEnd_5076607 := by
    simpa [prefixWord, tailWord_5076607, baseEnd_5076607] using wordTrace_append hprefix tailTrace_5076607
  have hstable : (prefixWord ++ tailWord_5076607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076607).length < 2 ^ (prefixWord ++ tailWord_5076607).sum := by decide
  have hdescent : baseEnd_5076607 < baseStart_5076607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076618 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_5076618 : Nat := 118140960795 + 5076618 * 2 ^ 59
def prefixEnd_5076618 : Nat := 4983230072969 + 3 ^ 40 * 5076618 * 2
def baseEnd_5076618 : Nat := 2606745133266723942428065

theorem tailTrace_5076618 : CollatzResearch.WordTrace tailWord_5076618 prefixEnd_5076618 2606745133266723942428065 := by
  unfold tailWord_5076618
  simp only [CollatzResearch.WordTrace]
  refine ⟨46289867480571869543183627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123439646614858318781823005 46289867480571869543183627)
  ·
    refine ⟨69434801220857804314775441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46289867480571869543183627 69434801220857804314775441)
    ·
      refine ⟨52076100915643353236081581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69434801220857804314775441 52076100915643353236081581)
      ·
        refine ⟨19528537843366257463530593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52076100915643353236081581 19528537843366257463530593)
        ·
          refine ⟨14646403382524693097647945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19528537843366257463530593 14646403382524693097647945)
          ·
            refine ⟨10984802536893519823235959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14646403382524693097647945 10984802536893519823235959)
            ·
              refine ⟨16477203805340279734853939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10984802536893519823235959 16477203805340279734853939)
              ·
                refine ⟨24715805708010419602280909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16477203805340279734853939 24715805708010419602280909)
                ·
                  refine ⟨9268427140503907350855341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24715805708010419602280909 9268427140503907350855341)
                  ·
                    refine ⟨3475660177688965256570753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9268427140503907350855341 3475660177688965256570753)
                    ·
                      refine ⟨2606745133266723942428065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475660177688965256570753 2606745133266723942428065)
                      ·
                        rfl

theorem cell23_5076618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_5076618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076618 prefixEnd_5076618 := by exact prefixLift 5076618
  have htrace : WordTrace (prefixWord ++ tailWord_5076618) baseStart_5076618 baseEnd_5076618 := by
    simpa [prefixWord, tailWord_5076618, baseEnd_5076618] using wordTrace_append hprefix tailTrace_5076618
  have hstable : (prefixWord ++ tailWord_5076618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076618).length < 2 ^ (prefixWord ++ tailWord_5076618).sum := by decide
  have hdescent : baseEnd_5076618 < baseStart_5076618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076631 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 3, 4, 2]
def baseStart_5076631 : Nat := 118140960795 + 5076631 * 2 ^ 59
def prefixEnd_5076631 : Nat := 4983230072969 + 3 ^ 40 * 5076631 * 2
def baseEnd_5076631 : Nat := 2606751808515232391565505

theorem tailTrace_5076631 : CollatzResearch.WordTrace tailWord_5076631 prefixEnd_5076631 2606751808515232391565505 := by
  unfold tailWord_5076631
  simp only [CollatzResearch.WordTrace]
  refine ⟨185159944071240381392957747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123439962714160254261971831 185159944071240381392957747)
  ·
    refine ⟨277739916106860572089436621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185159944071240381392957747 277739916106860572089436621)
    ·
      refine ⟨104152468540072714533538733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277739916106860572089436621 104152468540072714533538733)
      ·
        refine ⟨39057175702527267950077025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104152468540072714533538733 39057175702527267950077025)
        ·
          refine ⟨29292881776895450962557769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39057175702527267950077025 29292881776895450962557769)
          ·
            refine ⟨21969661332671588221918327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29292881776895450962557769 21969661332671588221918327)
            ·
              refine ⟨32954491999007382332877491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21969661332671588221918327 32954491999007382332877491)
              ·
                refine ⟨49431737998511073499316237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32954491999007382332877491 49431737998511073499316237)
                ·
                  refine ⟨18536901749441652562243589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49431737998511073499316237 18536901749441652562243589)
                  ·
                    refine ⟨3475669078020309855420673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18536901749441652562243589 3475669078020309855420673)
                    ·
                      refine ⟨2606751808515232391565505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475669078020309855420673 2606751808515232391565505)
                      ·
                        rfl

theorem cell23_5076631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_5076631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076631 prefixEnd_5076631 := by exact prefixLift 5076631
  have htrace : WordTrace (prefixWord ++ tailWord_5076631) baseStart_5076631 baseEnd_5076631 := by
    simpa [prefixWord, tailWord_5076631, baseEnd_5076631] using wordTrace_append hprefix tailTrace_5076631
  have hstable : (prefixWord ++ tailWord_5076631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076631).length < 2 ^ (prefixWord ++ tailWord_5076631).sum := by decide
  have hdescent : baseEnd_5076631 < baseStart_5076631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076642 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5076642 : Nat := 118140960795 + 5076642 * 2 ^ 59
def prefixEnd_5076642 : Nat := 4983230072969 + 3 ^ 40 * 5076642 * 2
def baseEnd_5076642 : Nat := 2606757456802431848527955

theorem tailTrace_5076642 : CollatzResearch.WordTrace tailWord_5076642 prefixEnd_5076642 2606757456802431848527955 := by
  unfold tailWord_5076642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46290086318550132567902045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123440230182800353514405453 46290086318550132567902045)
  ·
    refine ⟨17358782369456299712963267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46290086318550132567902045 17358782369456299712963267)
    ·
      refine ⟨26038173554184449569444901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17358782369456299712963267 26038173554184449569444901)
      ·
        refine ⟨4882157541409584294270919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26038173554184449569444901 4882157541409584294270919)
        ·
          refine ⟨7323236312114376441406379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882157541409584294270919 7323236312114376441406379)
          ·
            refine ⟨10984854468171564662109569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7323236312114376441406379 10984854468171564662109569)
            ·
              refine ⟨8238640851128673496582177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10984854468171564662109569 8238640851128673496582177)
              ·
                refine ⟨6178980638346505122436633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8238640851128673496582177 6178980638346505122436633)
                ·
                  refine ⟨4634235478759878841827475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6178980638346505122436633 4634235478759878841827475)
                  ·
                    refine ⟨6951353218139818262741213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4634235478759878841827475 6951353218139818262741213)
                    ·
                      refine ⟨2606757456802431848527955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951353218139818262741213 2606757456802431848527955)
                      ·
                        rfl

theorem cell23_5076642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5076642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076642 prefixEnd_5076642 := by exact prefixLift 5076642
  have htrace : WordTrace (prefixWord ++ tailWord_5076642) baseStart_5076642 baseEnd_5076642 := by
    simpa [prefixWord, tailWord_5076642, baseEnd_5076642] using wordTrace_append hprefix tailTrace_5076642
  have hstable : (prefixWord ++ tailWord_5076642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076642).length < 2 ^ (prefixWord ++ tailWord_5076642).sum := by decide
  have hdescent : baseEnd_5076642 < baseStart_5076642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076738 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5076738 : Nat := 118140960795 + 5076738 * 2 ^ 59
def prefixEnd_5076738 : Nat := 4983230072969 + 3 ^ 40 * 5076738 * 2
def baseEnd_5076738 : Nat := 2606806750945263472927513

theorem tailTrace_5076738 : CollatzResearch.WordTrace tailWord_5076738 prefixEnd_5076738 2606806750945263472927513 := by
  unfold tailWord_5076738
  simp only [CollatzResearch.WordTrace]
  refine ⟨46290961670463184666775717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123442564454568492444735245 46290961670463184666775717)
  ·
    refine ⟨8679555313211847125020447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46290961670463184666775717 8679555313211847125020447)
    ·
      refine ⟨13019332969817770687530671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8679555313211847125020447 13019332969817770687530671)
      ·
        refine ⟨19528999454726656031296007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13019332969817770687530671 19528999454726656031296007)
        ·
          refine ⟨29293499182089984046944011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19528999454726656031296007 29293499182089984046944011)
          ·
            refine ⟨43940248773134976070416017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29293499182089984046944011 43940248773134976070416017)
            ·
              refine ⟨32955186579851232052812013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43940248773134976070416017 32955186579851232052812013)
              ·
                refine ⟨12358194967444212019804505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32955186579851232052812013 12358194967444212019804505)
                ·
                  refine ⟨9268646225583159014853379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12358194967444212019804505 9268646225583159014853379)
                  ·
                    refine ⟨13902969338374738522280069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9268646225583159014853379 13902969338374738522280069)
                    ·
                      refine ⟨2606806750945263472927513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13902969338374738522280069 2606806750945263472927513)
                      ·
                        rfl

theorem cell23_5076738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5076738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076738 prefixEnd_5076738 := by exact prefixLift 5076738
  have htrace : WordTrace (prefixWord ++ tailWord_5076738) baseStart_5076738 baseEnd_5076738 := by
    simpa [prefixWord, tailWord_5076738, baseEnd_5076738] using wordTrace_append hprefix tailTrace_5076738
  have hstable : (prefixWord ++ tailWord_5076738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076738).length < 2 ^ (prefixWord ++ tailWord_5076738).sum := by decide
  have hdescent : baseEnd_5076738 < baseStart_5076738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076744 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 10]
def baseStart_5076744 : Nat := 118140960795 + 5076744 * 2 ^ 59
def prefixEnd_5076744 : Nat := 4983230072969 + 3 ^ 40 * 5076744 * 2
def baseEnd_5076744 : Nat := 289645536869910049939165

theorem tailTrace_5076744 : CollatzResearch.WordTrace tailWord_5076744 prefixEnd_5076744 289645536869910049939165 := by
  unfold tailWord_5076744
  simp only [CollatzResearch.WordTrace]
  refine ⟨92582032759915500845910643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123442710346554001127880857 92582032759915500845910643)
  ·
    refine ⟨138873049139873251268865965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92582032759915500845910643 138873049139873251268865965)
    ·
      refine ⟨52077393427452469225824737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138873049139873251268865965 52077393427452469225824737)
      ·
        refine ⟨39058045070589351919368553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52077393427452469225824737 39058045070589351919368553)
        ·
          refine ⟨29293533802942013939526415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39058045070589351919368553 29293533802942013939526415)
          ·
            refine ⟨43940300704413020909289623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29293533802942013939526415 43940300704413020909289623)
            ·
              refine ⟨65910451056619531363934435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43940300704413020909289623 65910451056619531363934435)
              ·
                refine ⟨98865676584929297045901653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65910451056619531363934435 98865676584929297045901653)
                ·
                  refine ⟨289645536869910049939165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 98865676584929297045901653 289645536869910049939165)
                  ·
                    rfl

theorem cell23_5076744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 10].length) (baseStart_5076744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076744 prefixEnd_5076744 := by exact prefixLift 5076744
  have htrace : WordTrace (prefixWord ++ tailWord_5076744) baseStart_5076744 baseEnd_5076744 := by
    simpa [prefixWord, tailWord_5076744, baseEnd_5076744] using wordTrace_append hprefix tailTrace_5076744
  have hstable : (prefixWord ++ tailWord_5076744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076744).length < 2 ^ (prefixWord ++ tailWord_5076744).sum := by decide
  have hdescent : baseEnd_5076744 < baseStart_5076744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076791 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 1, 5]
def baseStart_5076791 : Nat := 118140960795 + 5076791 * 2 ^ 59
def prefixEnd_5076791 : Nat := 4983230072969 + 3 ^ 40 * 5076791 * 2
def baseEnd_5076791 : Nat := 868944655139983921854923

theorem tailTrace_5076791 : CollatzResearch.WordTrace tailWord_5076791 prefixEnd_5076791 868944655139983921854923 := by
  unfold tailWord_5076791
  simp only [CollatzResearch.WordTrace]
  refine ⟨185165779750660728718782227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123443853167107152479188151 185165779750660728718782227)
  ·
    refine ⟨277748669625991093078173341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185165779750660728718782227 277748669625991093078173341)
    ·
      refine ⟨104155751109746659904315003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277748669625991093078173341 104155751109746659904315003)
      ·
        refine ⟨156233626664619989856472505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104155751109746659904315003 156233626664619989856472505)
        ·
          refine ⟨117175219998464992392354379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156233626664619989856472505 117175219998464992392354379)
          ·
            refine ⟨175762829997697488588531569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117175219998464992392354379 175762829997697488588531569)
            ·
              refine ⟨131822122498273116441398677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175762829997697488588531569 131822122498273116441398677)
              ·
                refine ⟨6179161992106552333190563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131822122498273116441398677 6179161992106552333190563)
                ·
                  refine ⟨9268742988159828499785845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179161992106552333190563 9268742988159828499785845)
                  ·
                    refine ⟨868944655139983921854923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9268742988159828499785845 868944655139983921854923)
                    ·
                      rfl

theorem cell23_5076791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_5076791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076791 prefixEnd_5076791 := by exact prefixLift 5076791
  have htrace : WordTrace (prefixWord ++ tailWord_5076791) baseStart_5076791 baseEnd_5076791 := by
    simpa [prefixWord, tailWord_5076791, baseEnd_5076791] using wordTrace_append hprefix tailTrace_5076791
  have hstable : (prefixWord ++ tailWord_5076791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076791).length < 2 ^ (prefixWord ++ tailWord_5076791).sum := by decide
  have hdescent : baseEnd_5076791 < baseStart_5076791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076805 : List Nat := [1, 3, 1, 1, 1, 2, 4, 5, 1, 1, 3]
def baseStart_5076805 : Nat := 118140960795 + 5076805 * 2 ^ 59
def prefixEnd_5076805 : Nat := 4983230072969 + 3 ^ 40 * 5076805 * 2
def baseEnd_5076805 : Nat := 2606841154149114710789705

theorem tailTrace_5076805 : CollatzResearch.WordTrace tailWord_5076805 prefixEnd_5076805 2606841154149114710789705 := by
  unfold tailWord_5076805
  simp only [CollatzResearch.WordTrace]
  refine ⟨185166290372610009109791869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123444193581740006073194579 185166290372610009109791869)
  ·
    refine ⟨69437358889728753416171951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185166290372610009109791869 69437358889728753416171951)
    ·
      refine ⟨104156038334593130124257927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69437358889728753416171951 104156038334593130124257927)
      ·
        refine ⟨156234057501889695186386891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104156038334593130124257927 156234057501889695186386891)
        ·
          refine ⟨234351086252834542779580337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156234057501889695186386891 234351086252834542779580337)
          ·
            refine ⟨175763314689625907084685253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234351086252834542779580337 175763314689625907084685253)
            ·
              refine ⟨32955621504304857578378485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175763314689625907084685253 32955621504304857578378485)
              ·
                refine ⟨3089589516028580397972983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32955621504304857578378485 3089589516028580397972983)
                ·
                  refine ⟨4634384274042870596959475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089589516028580397972983 4634384274042870596959475)
                  ·
                    refine ⟨6951576411064305895439213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4634384274042870596959475 6951576411064305895439213)
                    ·
                      refine ⟨2606841154149114710789705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951576411064305895439213 2606841154149114710789705)
                      ·
                        rfl

theorem cell23_5076805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_5076805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076805 prefixEnd_5076805 := by exact prefixLift 5076805
  have htrace : WordTrace (prefixWord ++ tailWord_5076805) baseStart_5076805 baseEnd_5076805 := by
    simpa [prefixWord, tailWord_5076805, baseEnd_5076805] using wordTrace_append hprefix tailTrace_5076805
  have hstable : (prefixWord ++ tailWord_5076805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076805).length < 2 ^ (prefixWord ++ tailWord_5076805).sum := by decide
  have hdescent : baseEnd_5076805 < baseStart_5076805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076845 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_5076845 : Nat := 118140960795 + 5076845 * 2 ^ 59
def prefixEnd_5076845 : Nat := 4983230072969 + 3 ^ 40 * 5076845 * 2
def baseEnd_5076845 : Nat := 2606861693375294554289521

theorem tailTrace_5076845 : CollatzResearch.WordTrace tailWord_5076845 prefixEnd_5076845 2606861693375294554289521 := by
  unfold tailWord_5076845
  simp only [CollatzResearch.WordTrace]
  refine ⟨185167749292465095941247989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123445166194976730627498659 185167749292465095941247989)
  ·
    refine ⟨17359476496168602744491999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185167749292465095941247989 17359476496168602744491999)
    ·
      refine ⟨26039214744252904116737999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17359476496168602744491999 26039214744252904116737999)
      ·
        refine ⟨39058822116379356175106999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26039214744252904116737999 39058822116379356175106999)
        ·
          refine ⟨58588233174569034262660499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39058822116379356175106999 58588233174569034262660499)
          ·
            refine ⟨87882349761853551393990749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58588233174569034262660499 87882349761853551393990749)
            ·
              refine ⟨32955881160695081772746531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87882349761853551393990749 32955881160695081772746531)
              ·
                refine ⟨49433821741042622659119797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32955881160695081772746531 49433821741042622659119797)
                ·
                  refine ⟨4634420788222745874292481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49433821741042622659119797 4634420788222745874292481)
                  ·
                    refine ⟨3475815591167059405719361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4634420788222745874292481 3475815591167059405719361)
                    ·
                      refine ⟨2606861693375294554289521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475815591167059405719361 2606861693375294554289521)
                      ·
                        rfl

theorem cell23_5076845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_5076845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076845 prefixEnd_5076845 := by exact prefixLift 5076845
  have htrace : WordTrace (prefixWord ++ tailWord_5076845) baseStart_5076845 baseEnd_5076845 := by
    simpa [prefixWord, tailWord_5076845, baseEnd_5076845] using wordTrace_append hprefix tailTrace_5076845
  have hstable : (prefixWord ++ tailWord_5076845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076845).length < 2 ^ (prefixWord ++ tailWord_5076845).sum := by decide
  have hdescent : baseEnd_5076845 < baseStart_5076845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076848 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3]
def baseStart_5076848 : Nat := 118140960795 + 5076848 * 2 ^ 59
def prefixEnd_5076848 : Nat := 4983230072969 + 3 ^ 40 * 5076848 * 2
def baseEnd_5076848 : Nat := 2606863233817258042552007

theorem tailTrace_5076848 : CollatzResearch.WordTrace tailWord_5076848 prefixEnd_5076848 2606863233817258042552007 := by
  unfold tailWord_5076848
  simp only [CollatzResearch.WordTrace]
  refine ⟨92583929355727113726803599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123445239140969484969071465 92583929355727113726803599)
  ·
    refine ⟨138875894033590670590205399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92583929355727113726803599 138875894033590670590205399)
    ·
      refine ⟨208313841050386005885308099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138875894033590670590205399 208313841050386005885308099)
      ·
        refine ⟨312470761575579008827962149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208313841050386005885308099 312470761575579008827962149)
        ·
          refine ⟨58588267795421064155242903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312470761575579008827962149 58588267795421064155242903)
          ·
            refine ⟨87882401693131596232864355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58588267795421064155242903 87882401693131596232864355)
            ·
              refine ⟨131823602539697394349296533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87882401693131596232864355 131823602539697394349296533)
              ·
                refine ⟨6179231369048315360123275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131823602539697394349296533 6179231369048315360123275)
                ·
                  refine ⟨9268847053572473040184913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179231369048315360123275 9268847053572473040184913)
                  ·
                    refine ⟨6951635290179354780138685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9268847053572473040184913 6951635290179354780138685)
                    ·
                      refine ⟨2606863233817258042552007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951635290179354780138685 2606863233817258042552007)
                      ·
                        rfl

theorem cell23_5076848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_5076848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076848 prefixEnd_5076848 := by exact prefixLift 5076848
  have htrace : WordTrace (prefixWord ++ tailWord_5076848) baseStart_5076848 baseEnd_5076848 := by
    simpa [prefixWord, tailWord_5076848, baseEnd_5076848] using wordTrace_append hprefix tailTrace_5076848
  have hstable : (prefixWord ++ tailWord_5076848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076848).length < 2 ^ (prefixWord ++ tailWord_5076848).sum := by decide
  have hdescent : baseEnd_5076848 < baseStart_5076848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076862 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5076862 : Nat := 118140960795 + 5076862 * 2 ^ 59
def prefixEnd_5076862 : Nat := 4983230072969 + 3 ^ 40 * 5076862 * 2
def baseEnd_5076862 : Nat := 2606870422546420987776943

theorem tailTrace_5076862 : CollatzResearch.WordTrace tailWord_5076862 prefixEnd_5076862 2606870422546420987776943 := by
  unfold tailWord_5076862
  simp only [CollatzResearch.WordTrace]
  refine ⟨23146046166675438480577105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123445579555602338563077893 23146046166675438480577105)
  ·
    refine ⟨17359534625006578860432829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23146046166675438480577105 17359534625006578860432829)
    ·
      refine ⟨6509825484377467072662311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17359534625006578860432829 6509825484377467072662311)
      ·
        refine ⟨9764738226566200608993467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6509825484377467072662311 9764738226566200608993467)
        ·
          refine ⟨14647107339849300913490201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9764738226566200608993467 14647107339849300913490201)
          ·
            refine ⟨10985330504886975685117651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14647107339849300913490201 10985330504886975685117651)
            ·
              refine ⟨16477995757330463527676477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10985330504886975685117651 16477995757330463527676477)
              ·
                refine ⟨6179248408998923822878679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16477995757330463527676477 6179248408998923822878679)
                ·
                  refine ⟨9268872613498385734318019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179248408998923822878679 9268872613498385734318019)
                  ·
                    refine ⟨13903308920247578601477029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9268872613498385734318019 13903308920247578601477029)
                    ·
                      refine ⟨2606870422546420987776943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13903308920247578601477029 2606870422546420987776943)
                      ·
                        rfl

theorem cell23_5076862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5076862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076862 prefixEnd_5076862 := by exact prefixLift 5076862
  have htrace : WordTrace (prefixWord ++ tailWord_5076862) baseStart_5076862 baseEnd_5076862 := by
    simpa [prefixWord, tailWord_5076862, baseEnd_5076862] using wordTrace_append hprefix tailTrace_5076862
  have hstable : (prefixWord ++ tailWord_5076862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076862).length < 2 ^ (prefixWord ++ tailWord_5076862).sum := by decide
  have hdescent : baseEnd_5076862 < baseStart_5076862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076872 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 2, 4]
def baseStart_5076872 : Nat := 118140960795 + 5076872 * 2 ^ 59
def prefixEnd_5076872 : Nat := 4983230072969 + 3 ^ 40 * 5076872 * 2
def baseEnd_5076872 : Nat := 868958519117655316217299

theorem tailTrace_5076872 : CollatzResearch.WordTrace tailWord_5076872 prefixEnd_5076872 868958519117655316217299 := by
  unfold tailWord_5076872
  simp only [CollatzResearch.WordTrace]
  refine ⟨92584367031683639776240435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123445822708911519701653913 92584367031683639776240435)
  ·
    refine ⟨138876550547525459664360653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92584367031683639776240435 138876550547525459664360653)
    ·
      refine ⟨52078706455322047374135245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138876550547525459664360653 52078706455322047374135245)
      ·
        refine ⟨19529514920745767765300717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52078706455322047374135245 19529514920745767765300717)
        ·
          refine ⟨7323568095279662911987769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19529514920745767765300717 7323568095279662911987769)
          ·
            refine ⟨5492676071459747183990827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7323568095279662911987769 5492676071459747183990827)
            ·
              refine ⟨8239014107189620775986241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5492676071459747183990827 8239014107189620775986241)
              ·
                refine ⟨6179260580392215581989681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8239014107189620775986241 6179260580392215581989681)
                ·
                  refine ⟨4634445435294161686492261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6179260580392215581989681 4634445435294161686492261)
                  ·
                    refine ⟨868958519117655316217299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4634445435294161686492261 868958519117655316217299)
                    ·
                      rfl

theorem cell23_5076872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_5076872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076872 prefixEnd_5076872 := by exact prefixLift 5076872
  have htrace : WordTrace (prefixWord ++ tailWord_5076872) baseStart_5076872 baseEnd_5076872 := by
    simpa [prefixWord, tailWord_5076872, baseEnd_5076872] using wordTrace_append hprefix tailTrace_5076872
  have hstable : (prefixWord ++ tailWord_5076872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076872).length < 2 ^ (prefixWord ++ tailWord_5076872).sum := by decide
  have hdescent : baseEnd_5076872 < baseStart_5076872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076901 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_5076901 : Nat := 118140960795 + 5076901 * 2 ^ 59
def prefixEnd_5076901 : Nat := 4983230072969 + 3 ^ 40 * 5076901 * 2
def baseEnd_5076901 : Nat := 2606890448291946335189263

theorem tailTrace_5076901 : CollatzResearch.WordTrace tailWord_5076901 prefixEnd_5076901 2606890448291946335189263 := by
  unfold tailWord_5076901
  simp only [CollatzResearch.WordTrace]
  refine ⟨185169791780262217505286557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123446527853508145003524371 185169791780262217505286557)
  ·
    refine ⟨69438671917598331564482459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185169791780262217505286557 69438671917598331564482459)
    ·
      refine ⟨104158007876397497346723689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69438671917598331564482459 104158007876397497346723689)
      ·
        refine ⟨78118505907298123010042767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104158007876397497346723689 78118505907298123010042767)
        ·
          refine ⟨117177758860947184515064151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78118505907298123010042767 117177758860947184515064151)
          ·
            refine ⟨175766638291420776772596227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117177758860947184515064151 175766638291420776772596227)
            ·
              refine ⟨263649957437131165158894341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175766638291420776772596227 263649957437131165158894341)
              ·
                refine ⟨49434367019462093467292689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263649957437131165158894341 49434367019462093467292689)
                ·
                  refine ⟨37075775264596570100469517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49434367019462093467292689 37075775264596570100469517)
                  ·
                    refine ⟨13903415724223713787676069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37075775264596570100469517 13903415724223713787676069)
                    ·
                      refine ⟨2606890448291946335189263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13903415724223713787676069 2606890448291946335189263)
                      ·
                        rfl

theorem cell23_5076901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_5076901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076901 prefixEnd_5076901 := by exact prefixLift 5076901
  have htrace : WordTrace (prefixWord ++ tailWord_5076901) baseStart_5076901 baseEnd_5076901 := by
    simpa [prefixWord, tailWord_5076901, baseEnd_5076901] using wordTrace_append hprefix tailTrace_5076901
  have hstable : (prefixWord ++ tailWord_5076901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076901).length < 2 ^ (prefixWord ++ tailWord_5076901).sum := by decide
  have hdescent : baseEnd_5076901 < baseStart_5076901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076946 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5076946 : Nat := 118140960795 + 5076946 * 2 ^ 59
def prefixEnd_5076946 : Nat := 4983230072969 + 3 ^ 40 * 5076946 * 2
def baseEnd_5076946 : Nat := 2606913554921398659126557

theorem tailTrace_5076946 : CollatzResearch.WordTrace tailWord_5076946 prefixEnd_5076946 2606913554921398659126557 := by
  unfold tailWord_5076946
  simp only [CollatzResearch.WordTrace]
  refine ⟨46292858266274797547668673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123447622043399460127116461 46292858266274797547668673)
  ·
    refine ⟨34719643699706098160751505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46292858266274797547668673 34719643699706098160751505)
    ·
      refine ⟨26039732774779573620563629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34719643699706098160751505 26039732774779573620563629)
      ·
        refine ⟨9764899790542340107711361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26039732774779573620563629 9764899790542340107711361)
        ·
          refine ⟨7323674842906755080783521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9764899790542340107711361 7323674842906755080783521)
          ·
            refine ⟨5492756132180066310587641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7323674842906755080783521 5492756132180066310587641)
            ·
              refine ⟨4119567099135049732940731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5492756132180066310587641 4119567099135049732940731)
              ·
                refine ⟨6179350648702574599411097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119567099135049732940731 6179350648702574599411097)
                ·
                  refine ⟨4634512986526930949558323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6179350648702574599411097 4634512986526930949558323)
                  ·
                    refine ⟨6951769479790396424337485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4634512986526930949558323 6951769479790396424337485)
                    ·
                      refine ⟨2606913554921398659126557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951769479790396424337485 2606913554921398659126557)
                      ·
                        rfl

theorem cell23_5076946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5076946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076946 prefixEnd_5076946 := by exact prefixLift 5076946
  have htrace : WordTrace (prefixWord ++ tailWord_5076946) baseStart_5076946 baseEnd_5076946 := by
    simpa [prefixWord, tailWord_5076946, baseEnd_5076946] using wordTrace_append hprefix tailTrace_5076946
  have hstable : (prefixWord ++ tailWord_5076946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076946).length < 2 ^ (prefixWord ++ tailWord_5076946).sum := by decide
  have hdescent : baseEnd_5076946 < baseStart_5076946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076948 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5076948 : Nat := 118140960795 + 5076948 * 2 ^ 59
def prefixEnd_5076948 : Nat := 4983230072969 + 3 ^ 40 * 5076948 * 2
def baseEnd_5076948 : Nat := 2606914581882707651301547

theorem tailTrace_5076948 : CollatzResearch.WordTrace tailWord_5076948 prefixEnd_5076948 2606914581882707651301547 := by
  unfold tailWord_5076948
  simp only [CollatzResearch.WordTrace]
  refine ⟨92585753005545972266123749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123447670674061296354831665 92585753005545972266123749)
  ·
    refine ⟨17359828688539869799898203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92585753005545972266123749 17359828688539869799898203)
    ·
      refine ⟨26039743032809804699847305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17359828688539869799898203 26039743032809804699847305)
      ·
        refine ⟨19529807274607353524885479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26039743032809804699847305 19529807274607353524885479)
        ·
          refine ⟨29294710911911030287328219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19529807274607353524885479 29294710911911030287328219)
          ·
            refine ⟨43942066367866545430992329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29294710911911030287328219 43942066367866545430992329)
            ·
              refine ⟨32956549775899909073244247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43942066367866545430992329 32956549775899909073244247)
              ·
                refine ⟨49434824663849863609866371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32956549775899909073244247 49434824663849863609866371)
                ·
                  refine ⟨74152236995774795414799557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49434824663849863609866371 74152236995774795414799557)
                  ·
                    refine ⟨13903544436707774140274917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74152236995774795414799557 13903544436707774140274917)
                    ·
                      refine ⟨2606914581882707651301547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13903544436707774140274917 2606914581882707651301547)
                      ·
                        rfl

theorem cell23_5076948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5076948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076948 prefixEnd_5076948 := by exact prefixLift 5076948
  have htrace : WordTrace (prefixWord ++ tailWord_5076948) baseStart_5076948 baseEnd_5076948 := by
    simpa [prefixWord, tailWord_5076948, baseEnd_5076948] using wordTrace_append hprefix tailTrace_5076948
  have hstable : (prefixWord ++ tailWord_5076948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076948).length < 2 ^ (prefixWord ++ tailWord_5076948).sum := by decide
  have hdescent : baseEnd_5076948 < baseStart_5076948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076952 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2]
def baseStart_5076952 : Nat := 118140960795 + 5076952 * 2 ^ 59
def prefixEnd_5076952 : Nat := 4983230072969 + 3 ^ 40 * 5076952 * 2
def baseEnd_5076952 : Nat := 2606916635805325635651529

theorem tailTrace_5076952 : CollatzResearch.WordTrace tailWord_5076952 prefixEnd_5076952 2606916635805325635651529 := by
  unfold tailWord_5076952
  simp only [CollatzResearch.WordTrace]
  refine ⟨92585825951538726607696555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123447767935384968810262073 92585825951538726607696555)
  ·
    refine ⟨138878738927308089911544833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92585825951538726607696555 138878738927308089911544833)
    ·
      refine ⟨104159054195481067433658625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138878738927308089911544833 104159054195481067433658625)
      ·
        refine ⟨78119290646610800575243969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104159054195481067433658625 78119290646610800575243969)
        ·
          refine ⟨58589467984958100431432977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78119290646610800575243969 58589467984958100431432977)
          ·
            refine ⟨43942100988718575323574733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58589467984958100431432977 43942100988718575323574733)
            ·
              refine ⟨16478287870769465746340525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43942100988718575323574733 16478287870769465746340525)
              ·
                refine ⟨6179357951538549654877697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16478287870769465746340525 6179357951538549654877697)
                ·
                  refine ⟨4634518463653912241158273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6179357951538549654877697 4634518463653912241158273)
                  ·
                    refine ⟨3475888847740434180868705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4634518463653912241158273 3475888847740434180868705)
                    ·
                      refine ⟨2606916635805325635651529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475888847740434180868705 2606916635805325635651529)
                      ·
                        rfl

theorem cell23_5076952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_5076952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076952 prefixEnd_5076952 := by exact prefixLift 5076952
  have htrace : WordTrace (prefixWord ++ tailWord_5076952) baseStart_5076952 baseEnd_5076952 := by
    simpa [prefixWord, tailWord_5076952, baseEnd_5076952] using wordTrace_append hprefix tailTrace_5076952
  have hstable : (prefixWord ++ tailWord_5076952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076952).length < 2 ^ (prefixWord ++ tailWord_5076952).sum := by decide
  have hdescent : baseEnd_5076952 < baseStart_5076952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076956 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5076956 : Nat := 118140960795 + 5076956 * 2 ^ 59
def prefixEnd_5076956 : Nat := 4983230072969 + 3 ^ 40 * 5076956 * 2
def baseEnd_5076956 : Nat := 2606918689727943620001511

theorem tailTrace_5076956 : CollatzResearch.WordTrace tailWord_5076956 prefixEnd_5076956 2606918689727943620001511 := by
  unfold tailWord_5076956
  simp only [CollatzResearch.WordTrace]
  refine ⟨92585898897531480949269361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123447865196708641265692481 92585898897531480949269361)
  ·
    refine ⟨69439424173148610711952021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92585898897531480949269361 69439424173148610711952021)
    ·
      refine ⟨3254973008116341127122751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69439424173148610711952021 3254973008116341127122751)
      ·
        refine ⟨4882459512174511690684127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254973008116341127122751 4882459512174511690684127)
        ·
          refine ⟨7323689268261767536026191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882459512174511690684127 7323689268261767536026191)
          ·
            refine ⟨10985533902392651304039287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7323689268261767536026191 10985533902392651304039287)
            ·
              refine ⟨16478300853588976956058931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10985533902392651304039287 16478300853588976956058931)
              ·
                refine ⟨24717451280383465434088397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16478300853588976956058931 24717451280383465434088397)
                ·
                  refine ⟨9269044230143799537783149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24717451280383465434088397 9269044230143799537783149)
                  ·
                    refine ⟨3475891586303924826668681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9269044230143799537783149 3475891586303924826668681)
                    ·
                      refine ⟨2606918689727943620001511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3475891586303924826668681 2606918689727943620001511)
                      ·
                        rfl

theorem cell23_5076956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5076956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076956 prefixEnd_5076956 := by exact prefixLift 5076956
  have htrace : WordTrace (prefixWord ++ tailWord_5076956) baseStart_5076956 baseEnd_5076956 := by
    simpa [prefixWord, tailWord_5076956, baseEnd_5076956] using wordTrace_append hprefix tailTrace_5076956
  have hstable : (prefixWord ++ tailWord_5076956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076956).length < 2 ^ (prefixWord ++ tailWord_5076956).sum := by decide
  have hdescent : baseEnd_5076956 < baseStart_5076956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076968 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_5076968 : Nat := 118140960795 + 5076968 * 2 ^ 59
def prefixEnd_5076968 : Nat := 4983230072969 + 3 ^ 40 * 5076968 * 2
def baseEnd_5076968 : Nat := 2606924851495797573051455

theorem tailTrace_5076968 : CollatzResearch.WordTrace tailWord_5076968 prefixEnd_5076968 2606924851495797573051455 := by
  unfold tailWord_5076968
  simp only [CollatzResearch.WordTrace]
  refine ⟨92586117735509743973987779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123448156980679658631983705 92586117735509743973987779)
  ·
    refine ⟨138879176603264615960981669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92586117735509743973987779 138879176603264615960981669)
    ·
      refine ⟨26039845613112115492684063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138879176603264615960981669 26039845613112115492684063)
      ·
        refine ⟨39059768419668173239026095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26039845613112115492684063 39059768419668173239026095)
        ·
          refine ⟨58589652629502259858539143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39059768419668173239026095 58589652629502259858539143)
          ·
            refine ⟨87884478944253389787808715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58589652629502259858539143 87884478944253389787808715)
            ·
              refine ⟨131826718416380084681713073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87884478944253389787808715 131826718416380084681713073)
              ·
                refine ⟨98870038812285063511284805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131826718416380084681713073 98870038812285063511284805)
                ·
                  refine ⟨18538132277303449408365901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98870038812285063511284805 18538132277303449408365901)
                  ·
                    refine ⟨6951799603988793528137213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18538132277303449408365901 6951799603988793528137213)
                    ·
                      refine ⟨2606924851495797573051455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951799603988793528137213 2606924851495797573051455)
                      ·
                        rfl

theorem cell23_5076968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_5076968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076968 prefixEnd_5076968 := by exact prefixLift 5076968
  have htrace : WordTrace (prefixWord ++ tailWord_5076968) baseStart_5076968 baseEnd_5076968 := by
    simpa [prefixWord, tailWord_5076968, baseEnd_5076968] using wordTrace_append hprefix tailTrace_5076968
  have hstable : (prefixWord ++ tailWord_5076968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076968).length < 2 ^ (prefixWord ++ tailWord_5076968).sum := by decide
  have hdescent : baseEnd_5076968 < baseStart_5076968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076971 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 1, 7]
def baseStart_5076971 : Nat := 118140960795 + 5076971 * 2 ^ 59
def prefixEnd_5076971 : Nat := 4983230072969 + 3 ^ 40 * 5076971 * 2
def baseEnd_5076971 : Nat := 868975463979253687104647

theorem tailTrace_5076971 : CollatzResearch.WordTrace tailWord_5076971 prefixEnd_5076971 868975463979253687104647 := by
  unfold tailWord_5076971
  simp only [CollatzResearch.WordTrace]
  refine ⟨185172344890008619460334767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123448229926672412973556511 185172344890008619460334767)
  ·
    refine ⟨277758517335012929190502151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185172344890008619460334767 277758517335012929190502151)
    ·
      refine ⟨416637776002519393785753227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277758517335012929190502151 416637776002519393785753227)
      ·
        refine ⟨624956664003779090678629841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416637776002519393785753227 624956664003779090678629841)
        ·
          refine ⟨468717498002834318008972381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624956664003779090678629841 468717498002834318008972381)
          ·
            refine ⟨175769061751062869253364643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468717498002834318008972381 175769061751062869253364643)
            ·
              refine ⟨263653592626594303880046965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175769061751062869253364643 263653592626594303880046965)
              ·
                refine ⟨24717524308743215988754403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263653592626594303880046965 24717524308743215988754403)
                ·
                  refine ⟨37076286463114823983131605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24717524308743215988754403 37076286463114823983131605)
                  ·
                    refine ⟨868975463979253687104647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37076286463114823983131605 868975463979253687104647)
                    ·
                      rfl

theorem cell23_5076971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 7].length) (baseStart_5076971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076971 prefixEnd_5076971 := by exact prefixLift 5076971
  have htrace : WordTrace (prefixWord ++ tailWord_5076971) baseStart_5076971 baseEnd_5076971 := by
    simpa [prefixWord, tailWord_5076971, baseEnd_5076971] using wordTrace_append hprefix tailTrace_5076971
  have hstable : (prefixWord ++ tailWord_5076971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076971).length < 2 ^ (prefixWord ++ tailWord_5076971).sum := by decide
  have hdescent : baseEnd_5076971 < baseStart_5076971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5076988 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_5076988 : Nat := 118140960795 + 5076988 * 2 ^ 59
def prefixEnd_5076988 : Nat := 4983230072969 + 3 ^ 40 * 5076988 * 2
def baseEnd_5076988 : Nat := 868978373702962498267121

theorem tailTrace_5076988 : CollatzResearch.WordTrace tailWord_5076988 prefixEnd_5076988 868978373702962498267121 := by
  unfold tailWord_5076988
  simp only [CollatzResearch.WordTrace]
  refine ⟨92586482465473515681851809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123448643287298020909135745 92586482465473515681851809)
  ·
    refine ⟨69439861849105136761388857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92586482465473515681851809 69439861849105136761388857)
    ·
      refine ⟨52079896386828852571041643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69439861849105136761388857 52079896386828852571041643)
      ·
        refine ⟨78119844580243278856562465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52079896386828852571041643 78119844580243278856562465)
        ·
          refine ⟨58589883435182459142421849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78119844580243278856562465 58589883435182459142421849)
          ·
            refine ⟨43942412576386844356816387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58589883435182459142421849 43942412576386844356816387)
            ·
              refine ⟨65913618864580266535224581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43942412576386844356816387 65913618864580266535224581)
              ·
                refine ⟨12358803537108799975354609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65913618864580266535224581 12358803537108799975354609)
                ·
                  refine ⟨9269102652831599981515957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12358803537108799975354609 9269102652831599981515957)
                  ·
                    refine ⟨868978373702962498267121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9269102652831599981515957 868978373702962498267121)
                    ·
                      rfl

theorem cell23_5076988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_5076988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5076988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5076988 prefixEnd_5076988 := by exact prefixLift 5076988
  have htrace : WordTrace (prefixWord ++ tailWord_5076988) baseStart_5076988 baseEnd_5076988 := by
    simpa [prefixWord, tailWord_5076988, baseEnd_5076988] using wordTrace_append hprefix tailTrace_5076988
  have hstable : (prefixWord ++ tailWord_5076988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5076988).length < 2 ^ (prefixWord ++ tailWord_5076988).sum := by decide
  have hdescent : baseEnd_5076988 < baseStart_5076988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5076988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077001 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 4, 8]
def baseStart_5077001 : Nat := 118140960795 + 5077001 * 2 ^ 59
def prefixEnd_5077001 : Nat := 4983230072969 + 3 ^ 40 * 5077001 * 2
def baseEnd_5077001 : Nat := 868980598785798647979601

theorem tailTrace_5077001 : CollatzResearch.WordTrace tailWord_5077001 prefixEnd_5077001 868980598785798647979601 := by
  unfold tailWord_5077001
  simp only [CollatzResearch.WordTrace]
  refine ⟨185173439079899934583926857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123448959386599956389284571 185173439079899934583926857)
  ·
    refine ⟨138880079309924950937945143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185173439079899934583926857 138880079309924950937945143)
    ·
      refine ⟨208320118964887426406917715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138880079309924950937945143 208320118964887426406917715)
      ·
        refine ⟨312480178447331139610376573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208320118964887426406917715 312480178447331139610376573)
        ·
          refine ⟨117180066917749177353891215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312480178447331139610376573 117180066917749177353891215)
          ·
            refine ⟨175770100376623766030836823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117180066917749177353891215 175770100376623766030836823)
            ·
              refine ⟨263655150564935649046255235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175770100376623766030836823 263655150564935649046255235)
              ·
                refine ⟨395482725847403473569382853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263655150564935649046255235 395482725847403473569382853)
                ·
                  refine ⟨74153011096388151294259285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395482725847403473569382853 74153011096388151294259285)
                  ·
                    refine ⟨868980598785798647979601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74153011096388151294259285 868980598785798647979601)
                    ·
                      rfl

theorem cell23_5077001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_5077001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077001 prefixEnd_5077001 := by exact prefixLift 5077001
  have htrace : WordTrace (prefixWord ++ tailWord_5077001) baseStart_5077001 baseEnd_5077001 := by
    simpa [prefixWord, tailWord_5077001, baseEnd_5077001] using wordTrace_append hprefix tailTrace_5077001
  have hstable : (prefixWord ++ tailWord_5077001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077001).length < 2 ^ (prefixWord ++ tailWord_5077001).sum := by decide
  have hdescent : baseEnd_5077001 < baseStart_5077001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077025 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_5077025 : Nat := 118140960795 + 5077025 * 2 ^ 59
def prefixEnd_5077025 : Nat := 4983230072969 + 3 ^ 40 * 5077025 * 2
def baseEnd_5077025 : Nat := 2606954119893103850038693

theorem tailTrace_5077025 : CollatzResearch.WordTrace tailWord_5077025 prefixEnd_5077025 2606954119893103850038693 := by
  unfold tailWord_5077025
  simp only [CollatzResearch.WordTrace]
  refine ⟨185174314431812986682800529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123449542954541991121867019 185174314431812986682800529)
  ·
    refine ⟨138880735823859740012100397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185174314431812986682800529 138880735823859740012100397)
    ·
      refine ⟨52080275933947402504537649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138880735823859740012100397 52080275933947402504537649)
      ·
        refine ⟨39060206950460551878403237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52080275933947402504537649 39060206950460551878403237)
        ·
          refine ⟨7323788803211353477200607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39060206950460551878403237 7323788803211353477200607)
          ·
            refine ⟨10985683204817030215800911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7323788803211353477200607 10985683204817030215800911)
            ·
              refine ⟨16478524807225545323701367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10985683204817030215800911 16478524807225545323701367)
              ·
                refine ⟨24717787210838317985552051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16478524807225545323701367 24717787210838317985552051)
                ·
                  refine ⟨37076680816257476978328077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24717787210838317985552051 37076680816257476978328077)
                  ·
                    refine ⟨13903755306096553866873029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37076680816257476978328077 13903755306096553866873029)
                    ·
                      refine ⟨2606954119893103850038693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13903755306096553866873029 2606954119893103850038693)
                      ·
                        rfl

theorem cell23_5077025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_5077025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077025 prefixEnd_5077025 := by exact prefixLift 5077025
  have htrace : WordTrace (prefixWord ++ tailWord_5077025) baseStart_5077025 baseEnd_5077025 := by
    simpa [prefixWord, tailWord_5077025, baseEnd_5077025] using wordTrace_append hprefix tailTrace_5077025
  have hstable : (prefixWord ++ tailWord_5077025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077025).length < 2 ^ (prefixWord ++ tailWord_5077025).sum := by decide
  have hdescent : baseEnd_5077025 < baseStart_5077025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077045 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_5077045 : Nat := 118140960795 + 5077045 * 2 ^ 59
def prefixEnd_5077045 : Nat := 4983230072969 + 3 ^ 40 * 5077045 * 2
def baseEnd_5077045 : Nat := 2606964389506193771788601

theorem tailTrace_5077045 : CollatzResearch.WordTrace tailWord_5077045 prefixEnd_5077045 2606964389506193771788601 := by
  unfold tailWord_5077045
  simp only [CollatzResearch.WordTrace]
  refine ⟨185175043891740530098528589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123450029261160353399019059 185175043891740530098528589)
  ·
    refine ⟨69440641459402698786948221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185175043891740530098528589 69440641459402698786948221)
    ·
      refine ⟨26040240547276012045105583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69440641459402698786948221 26040240547276012045105583)
      ·
        refine ⟨39060360820914018067658375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26040240547276012045105583 39060360820914018067658375)
        ·
          refine ⟨58590541231371027101487563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39060360820914018067658375 58590541231371027101487563)
          ·
            refine ⟨87885811847056540652231345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58590541231371027101487563 87885811847056540652231345)
            ·
              refine ⟨65914358885292405489173509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87885811847056540652231345 65914358885292405489173509)
              ·
                refine ⟨12358942290992326029220033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65914358885292405489173509 12358942290992326029220033)
                ·
                  refine ⟨9269206718244244521915025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12358942290992326029220033 9269206718244244521915025)
                  ·
                    refine ⟨6951905038683183391436269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9269206718244244521915025 6951905038683183391436269)
                    ·
                      refine ⟨2606964389506193771788601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951905038683183391436269 2606964389506193771788601)
                      ·
                        rfl

theorem cell23_5077045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_5077045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077045 prefixEnd_5077045 := by exact prefixLift 5077045
  have htrace : WordTrace (prefixWord ++ tailWord_5077045) baseStart_5077045 baseEnd_5077045 := by
    simpa [prefixWord, tailWord_5077045, baseEnd_5077045] using wordTrace_append hprefix tailTrace_5077045
  have hstable : (prefixWord ++ tailWord_5077045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077045).length < 2 ^ (prefixWord ++ tailWord_5077045).sum := by decide
  have hdescent : baseEnd_5077045 < baseStart_5077045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077052 : List Nat := [2, 2, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_5077052 : Nat := 118140960795 + 5077052 * 2 ^ 59
def prefixEnd_5077052 : Nat := 4983230072969 + 3 ^ 40 * 5077052 * 2
def baseEnd_5077052 : Nat := 868989327956925081467023

theorem tailTrace_5077052 : CollatzResearch.WordTrace tailWord_5077052 prefixEnd_5077052 868989327956925081467023 := by
  unfold tailWord_5077052
  simp only [CollatzResearch.WordTrace]
  refine ⟨92587649601357585147016705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123450199468476780196022273 92587649601357585147016705)
  ·
    refine ⟨69440737201018188860262529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92587649601357585147016705 69440737201018188860262529)
    ·
      refine ⟨52080552900763641645196897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69440737201018188860262529 52080552900763641645196897)
      ·
        refine ⟨39060414675572731233897673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52080552900763641645196897 39060414675572731233897673)
        ·
          refine ⟨29295311006679548425423255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39060414675572731233897673 29295311006679548425423255)
          ·
            refine ⟨43942966510019322638134883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29295311006679548425423255 43942966510019322638134883)
            ·
              refine ⟨65914449765028983957202325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43942966510019322638134883 65914449765028983957202325)
              ·
                refine ⟨3089739832735733622993859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65914449765028983957202325 3089739832735733622993859)
                ·
                  refine ⟨4634609749103600434490789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089739832735733622993859 4634609749103600434490789)
                  ·
                    refine ⟨868989327956925081467023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4634609749103600434490789 868989327956925081467023)
                    ·
                      rfl

theorem cell23_5077052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_5077052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077052 prefixEnd_5077052 := by exact prefixLift 5077052
  have htrace : WordTrace (prefixWord ++ tailWord_5077052) baseStart_5077052 baseEnd_5077052 := by
    simpa [prefixWord, tailWord_5077052, baseEnd_5077052] using wordTrace_append hprefix tailTrace_5077052
  have hstable : (prefixWord ++ tailWord_5077052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077052).length < 2 ^ (prefixWord ++ tailWord_5077052).sum := by decide
  have hdescent : baseEnd_5077052 < baseStart_5077052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077062 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5077062 : Nat := 118140960795 + 5077062 * 2 ^ 59
def prefixEnd_5077062 : Nat := 4983230072969 + 3 ^ 40 * 5077062 * 2
def baseEnd_5077062 : Nat := 2606973118677320205276023

theorem tailTrace_5077062 : CollatzResearch.WordTrace tailWord_5077062 prefixEnd_5077062 2606973118677320205276023 := by
  unfold tailWord_5077062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5786739497896216937559295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123450442621785961334598293 5786739497896216937559295)
  ·
    refine ⟨8680109246844325406338943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5786739497896216937559295 8680109246844325406338943)
    ·
      refine ⟨13020163870266488109508415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8680109246844325406338943 13020163870266488109508415)
      ·
        refine ⟨19530245805399732164262623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13020163870266488109508415 19530245805399732164262623)
        ·
          refine ⟨29295368708099598246393935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19530245805399732164262623 29295368708099598246393935)
          ·
            refine ⟨43943053062149397369590903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29295368708099598246393935 43943053062149397369590903)
            ·
              refine ⟨65914579593224096054386355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43943053062149397369590903 65914579593224096054386355)
              ·
                refine ⟨98871869389836144081579533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65914579593224096054386355 98871869389836144081579533)
                ·
                  refine ⟨37076951021188554030592325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98871869389836144081579533 37076951021188554030592325)
                  ·
                    refine ⟨6951928316472853880736061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37076951021188554030592325 6951928316472853880736061)
                    ·
                      refine ⟨2606973118677320205276023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6951928316472853880736061 2606973118677320205276023)
                      ·
                        rfl

theorem cell23_5077062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5077062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077062 prefixEnd_5077062 := by exact prefixLift 5077062
  have htrace : WordTrace (prefixWord ++ tailWord_5077062) baseStart_5077062 baseEnd_5077062 := by
    simpa [prefixWord, tailWord_5077062, baseEnd_5077062] using wordTrace_append hprefix tailTrace_5077062
  have hstable : (prefixWord ++ tailWord_5077062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077062).length < 2 ^ (prefixWord ++ tailWord_5077062).sum := by decide
  have hdescent : baseEnd_5077062 < baseStart_5077062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077065 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 6]
def baseStart_5077065 : Nat := 118140960795 + 5077065 * 2 ^ 59
def prefixEnd_5077065 : Nat := 4983230072969 + 3 ^ 40 * 5077065 * 2
def baseEnd_5077065 : Nat := 289663851013253743726501

theorem tailTrace_5077065 : CollatzResearch.WordTrace tailWord_5077065 prefixEnd_5077065 289663851013253743726501 := by
  unfold tailWord_5077065
  simp only [CollatzResearch.WordTrace]
  refine ⟨185175773351668073514256649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123450515567778715676171099 185175773351668073514256649)
  ·
    refine ⟨138881830013751055135692487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185175773351668073514256649 138881830013751055135692487)
    ·
      refine ⟨208322745020626582703538731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138881830013751055135692487 208322745020626582703538731)
      ·
        refine ⟨312484117530939874055308097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208322745020626582703538731 312484117530939874055308097)
        ·
          refine ⟨234363088148204905541481073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312484117530939874055308097 234363088148204905541481073)
          ·
            refine ⟨175772316111153679156110805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234363088148204905541481073 175772316111153679156110805)
            ·
              refine ⟨4119663658855164355221347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 175772316111153679156110805 4119663658855164355221347)
              ·
                refine ⟨6179495488282746532832021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119663658855164355221347 6179495488282746532832021)
                ·
                  refine ⟨289663851013253743726501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6179495488282746532832021 289663851013253743726501)
                  ·
                    rfl

theorem cell23_5077065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 6].length) (baseStart_5077065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077065 prefixEnd_5077065 := by exact prefixLift 5077065
  have htrace : WordTrace (prefixWord ++ tailWord_5077065) baseStart_5077065 baseEnd_5077065 := by
    simpa [prefixWord, tailWord_5077065, baseEnd_5077065] using wordTrace_append hprefix tailTrace_5077065
  have hstable : (prefixWord ++ tailWord_5077065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077065).length < 2 ^ (prefixWord ++ tailWord_5077065).sum := by decide
  have hdescent : baseEnd_5077065 < baseStart_5077065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077095 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 1, 5]
def baseStart_5077095 : Nat := 118140960795 + 5077095 * 2 ^ 59
def prefixEnd_5077095 : Nat := 4983230072969 + 3 ^ 40 * 5077095 * 2
def baseEnd_5077095 : Nat := 868996687846306192054457

theorem tailTrace_5077095 : CollatzResearch.WordTrace tailWord_5077095 prefixEnd_5077095 868996687846306192054457 := by
  unfold tailWord_5077095
  simp only [CollatzResearch.WordTrace]
  refine ⟨185176867541559388637848739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123451245027706259091899159 185176867541559388637848739)
  ·
    refine ⟨277765301312339082956773109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185176867541559388637848739 277765301312339082956773109)
    ·
      refine ⟨26040496998031789027197479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277765301312339082956773109 26040496998031789027197479)
      ·
        refine ⟨39060745497047683540796219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26040496998031789027197479 39060745497047683540796219)
        ·
          refine ⟨58591118245571525311194329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39060745497047683540796219 58591118245571525311194329)
          ·
            refine ⟨43943338684178643983395747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58591118245571525311194329 43943338684178643983395747)
            ·
              refine ⟨65915008026267965975093621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43943338684178643983395747 65915008026267965975093621)
              ·
                refine ⟨6179532002462621810165027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65915008026267965975093621 6179532002462621810165027)
                ·
                  refine ⟨9269298003693932715247541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179532002462621810165027 9269298003693932715247541)
                  ·
                    refine ⟨868996687846306192054457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9269298003693932715247541 868996687846306192054457)
                    ·
                      rfl

theorem cell23_5077095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_5077095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077095 prefixEnd_5077095 := by exact prefixLift 5077095
  have htrace : WordTrace (prefixWord ++ tailWord_5077095) baseStart_5077095 baseEnd_5077095 := by
    simpa [prefixWord, tailWord_5077095, baseEnd_5077095] using wordTrace_append hprefix tailTrace_5077095
  have hstable : (prefixWord ++ tailWord_5077095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077095).length < 2 ^ (prefixWord ++ tailWord_5077095).sum := by decide
  have hdescent : baseEnd_5077095 < baseStart_5077095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077149 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_5077149 : Nat := 118140960795 + 5077149 * 2 ^ 59
def prefixEnd_5077149 : Nat := 4983230072969 + 3 ^ 40 * 5077149 * 2
def baseEnd_5077149 : Nat := 2607017791494261364888123

theorem tailTrace_5077149 : CollatzResearch.WordTrace tailWord_5077149 prefixEnd_5077149 2607017791494261364888123 := by
  unfold tailWord_5077149
  simp only [CollatzResearch.WordTrace]
  refine ⟨185178837083363755860314501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123452558055575837240209667 185178837083363755860314501)
  ·
    refine ⟨34721031953130704223808969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185178837083363755860314501 34721031953130704223808969)
    ·
      refine ⟨26040773964848028167856727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34721031953130704223808969 26040773964848028167856727)
      ·
        refine ⟨39061160947272042251785091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26040773964848028167856727 39061160947272042251785091)
        ·
          refine ⟨58591741420908063377677637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39061160947272042251785091 58591741420908063377677637)
          ·
            refine ⟨10985951516420261883314557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58591741420908063377677637 10985951516420261883314557)
            ·
              refine ⟨4119731818657598206242959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10985951516420261883314557 4119731818657598206242959)
              ·
                refine ⟨6179597727986397309364439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119731818657598206242959 6179597727986397309364439)
                ·
                  refine ⟨9269396591979595964046659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179597727986397309364439 9269396591979595964046659)
                  ·
                    refine ⟨13904094887969393946069989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9269396591979595964046659 13904094887969393946069989)
                    ·
                      refine ⟨2607017791494261364888123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13904094887969393946069989 2607017791494261364888123)
                      ·
                        rfl

theorem cell23_5077149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_5077149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077149 prefixEnd_5077149 := by exact prefixLift 5077149
  have htrace : WordTrace (prefixWord ++ tailWord_5077149) baseStart_5077149 baseEnd_5077149 := by
    simpa [prefixWord, tailWord_5077149, baseEnd_5077149] using wordTrace_append hprefix tailTrace_5077149
  have hstable : (prefixWord ++ tailWord_5077149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077149).length < 2 ^ (prefixWord ++ tailWord_5077149).sum := by decide
  have hdescent : baseEnd_5077149 < baseStart_5077149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077152 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5]
def baseStart_5077152 : Nat := 118140960795 + 5077152 * 2 ^ 59
def prefixEnd_5077152 : Nat := 4983230072969 + 3 ^ 40 * 5077152 * 2
def baseEnd_5077152 : Nat := 2607019331936224853150609

theorem tailTrace_5077152 : CollatzResearch.WordTrace tailWord_5077152 prefixEnd_5077152 2607019331936224853150609 := by
  unfold tailWord_5077152
  simp only [CollatzResearch.WordTrace]
  refine ⟨92589473251176443686336855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123452631001568591581782473 92589473251176443686336855)
  ·
    refine ⟨138884209876764665529505283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92589473251176443686336855 138884209876764665529505283)
    ·
      refine ⟨208326314815146998294257925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138884209876764665529505283 208326314815146998294257925)
      ·
        refine ⟨39061184027840062180173361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208326314815146998294257925 39061184027840062180173361)
        ·
          refine ⟨29295888020880046635130021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39061184027840062180173361 29295888020880046635130021)
          ·
            refine ⟨5492979003915008744086879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29295888020880046635130021 5492979003915008744086879)
            ·
              refine ⟨8239468505872513116130319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5492979003915008744086879 8239468505872513116130319)
              ·
                refine ⟨12359202758808769674195479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8239468505872513116130319 12359202758808769674195479)
                ·
                  refine ⟨18538804138213154511293219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12359202758808769674195479 18538804138213154511293219)
                  ·
                    refine ⟨27808206207319731766939829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18538804138213154511293219 27808206207319731766939829)
                    ·
                      refine ⟨2607019331936224853150609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27808206207319731766939829 2607019331936224853150609)
                      ·
                        rfl

theorem cell23_5077152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_5077152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077152 prefixEnd_5077152 := by exact prefixLift 5077152
  have htrace : WordTrace (prefixWord ++ tailWord_5077152) baseStart_5077152 baseEnd_5077152 := by
    simpa [prefixWord, tailWord_5077152, baseEnd_5077152] using wordTrace_append hprefix tailTrace_5077152
  have hstable : (prefixWord ++ tailWord_5077152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077152).length < 2 ^ (prefixWord ++ tailWord_5077152).sum := by decide
  have hdescent : baseEnd_5077152 < baseStart_5077152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077186 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_5077186 : Nat := 118140960795 + 5077186 * 2 ^ 59
def prefixEnd_5077186 : Nat := 4983230072969 + 3 ^ 40 * 5077186 * 2
def baseEnd_5077186 : Nat := 2607036790278477720125453

theorem tailTrace_5077186 : CollatzResearch.WordTrace tailWord_5077186 prefixEnd_5077186 2607036790278477720125453 := by
  unfold tailWord_5077186
  simp only [CollatzResearch.WordTrace]
  refine ⟨46295046646057427794852853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123453457722819807452940941 46295046646057427794852853)
  ·
    refine ⟨4340160623067883855767455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46295046646057427794852853 4340160623067883855767455)
    ·
      refine ⟨6510240934601825783651183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340160623067883855767455 6510240934601825783651183)
      ·
        refine ⟨9765361401902738675476775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510240934601825783651183 9765361401902738675476775)
        ·
          refine ⟨14648042102854108013215163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9765361401902738675476775 14648042102854108013215163)
          ·
            refine ⟨21972063154281162019822745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14648042102854108013215163 21972063154281162019822745)
            ·
              refine ⟨16479047365710871514867059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21972063154281162019822745 16479047365710871514867059)
              ·
                refine ⟨24718571048566307272300589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16479047365710871514867059 24718571048566307272300589)
                ·
                  refine ⟨9269464143212365227112721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24718571048566307272300589 9269464143212365227112721)
                  ·
                    refine ⟨6952098107409273920334541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9269464143212365227112721 6952098107409273920334541)
                    ·
                      refine ⟨2607036790278477720125453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6952098107409273920334541 2607036790278477720125453)
                      ·
                        rfl

theorem cell23_5077186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_5077186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077186 prefixEnd_5077186 := by exact prefixLift 5077186
  have htrace : WordTrace (prefixWord ++ tailWord_5077186) baseStart_5077186 baseEnd_5077186 := by
    simpa [prefixWord, tailWord_5077186, baseEnd_5077186] using wordTrace_append hprefix tailTrace_5077186
  have hstable : (prefixWord ++ tailWord_5077186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077186).length < 2 ^ (prefixWord ++ tailWord_5077186).sum := by decide
  have hdescent : baseEnd_5077186 < baseStart_5077186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077235 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4]
def baseStart_5077235 : Nat := 118140960795 + 5077235 * 2 ^ 59
def prefixEnd_5077235 : Nat := 4983230072969 + 3 ^ 40 * 5077235 * 2
def baseEnd_5077235 : Nat := 2607061950830548028412727

theorem tailTrace_5077235 : CollatzResearch.WordTrace tailWord_5077235 prefixEnd_5077235 2607061950830548028412727 := by
  unfold tailWord_5077235
  simp only [CollatzResearch.WordTrace]
  refine ⟨185181973761052192547945159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123454649174034795031963439 185181973761052192547945159)
  ·
    refine ⟨277772960641578288821917739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185181973761052192547945159 277772960641578288821917739)
    ·
      refine ⟨416659440962367433232876609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277772960641578288821917739 416659440962367433232876609)
      ·
        refine ⟨312494580721775574924657457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416659440962367433232876609 312494580721775574924657457)
        ·
          refine ⟨234370935541331681193493093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312494580721775574924657457 234370935541331681193493093)
          ·
            refine ⟨43944550413999690223779955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234370935541331681193493093 43944550413999690223779955)
            ·
              refine ⟨65916825620999535335669933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43944550413999690223779955 65916825620999535335669933)
              ·
                refine ⟨24718809607874825750876225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65916825620999535335669933 24718809607874825750876225)
                ·
                  refine ⟨18539107205906119313157169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24718809607874825750876225 18539107205906119313157169)
                  ·
                    refine ⟨13904330404429589484867877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18539107205906119313157169 13904330404429589484867877)
                    ·
                      refine ⟨2607061950830548028412727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13904330404429589484867877 2607061950830548028412727)
                      ·
                        rfl

theorem cell23_5077235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_5077235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077235 prefixEnd_5077235 := by exact prefixLift 5077235
  have htrace : WordTrace (prefixWord ++ tailWord_5077235) baseStart_5077235 baseEnd_5077235 := by
    simpa [prefixWord, tailWord_5077235, baseEnd_5077235] using wordTrace_append hprefix tailTrace_5077235
  have hstable : (prefixWord ++ tailWord_5077235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077235).length < 2 ^ (prefixWord ++ tailWord_5077235).sum := by decide
  have hdescent : baseEnd_5077235 < baseStart_5077235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077275 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 4, 5]
def baseStart_5077275 : Nat := 118140960795 + 5077275 * 2 ^ 59
def prefixEnd_5077275 : Nat := 4983230072969 + 3 ^ 40 * 5077275 * 2
def baseEnd_5077275 : Nat := 869027496685575957304181

theorem tailTrace_5077275 : CollatzResearch.WordTrace tailWord_5077275 prefixEnd_5077275 869027496685575957304181 := by
  unfold tailWord_5077275
  simp only [CollatzResearch.WordTrace]
  refine ⟨185183432680907279379401279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123455621787271519586267519 185183432680907279379401279)
  ·
    refine ⟨277775149021360919069101919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185183432680907279379401279 277775149021360919069101919)
    ·
      refine ⟨416662723532041378603652879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277775149021360919069101919 416662723532041378603652879)
      ·
        refine ⟨624994085298062067905479319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416662723532041378603652879 624994085298062067905479319)
        ·
          refine ⟨937491127947093101858218979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624994085298062067905479319 937491127947093101858218979)
          ·
            refine ⟨1406236691920639652787328469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937491127947093101858218979 1406236691920639652787328469)
            ·
              refine ⟨32958672466889991862203011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1406236691920639652787328469 32958672466889991862203011)
              ·
                refine ⟨49438008700334987793304517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32958672466889991862203011 49438008700334987793304517)
                ·
                  refine ⟨9269626631312810211244597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49438008700334987793304517 9269626631312810211244597)
                  ·
                    refine ⟨869027496685575957304181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9269626631312810211244597 869027496685575957304181)
                    ·
                      rfl

theorem cell23_5077275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 5].length) (baseStart_5077275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077275 prefixEnd_5077275 := by exact prefixLift 5077275
  have htrace : WordTrace (prefixWord ++ tailWord_5077275) baseStart_5077275 baseEnd_5077275 := by
    simpa [prefixWord, tailWord_5077275, baseEnd_5077275] using wordTrace_append hprefix tailTrace_5077275
  have hstable : (prefixWord ++ tailWord_5077275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077275).length < 2 ^ (prefixWord ++ tailWord_5077275).sum := by decide
  have hdescent : baseEnd_5077275 < baseStart_5077275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077295 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_5077295 : Nat := 118140960795 + 5077295 * 2 ^ 59
def prefixEnd_5077295 : Nat := 4983230072969 + 3 ^ 40 * 5077295 * 2
def baseEnd_5077295 : Nat := 2607092759669817793662451

theorem tailTrace_5077295 : CollatzResearch.WordTrace tailWord_5077295 prefixEnd_5077295 2607092759669817793662451 := by
  unfold tailWord_5077295
  simp only [CollatzResearch.WordTrace]
  refine ⟨185184162140834822795129339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123456108093889881863419559 185184162140834822795129339)
  ·
    refine ⟨277776243211252234192694009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185184162140834822795129339 277776243211252234192694009)
    ·
      refine ⟨208332182408439175644520507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277776243211252234192694009 208332182408439175644520507)
      ·
        refine ⟨312498273612658763466780761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208332182408439175644520507 312498273612658763466780761)
        ·
          refine ⟨234373705209494072600085571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312498273612658763466780761 234373705209494072600085571)
          ·
            refine ⟨351560557814241108900128357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234373705209494072600085571 351560557814241108900128357)
            ·
              refine ⟨65917604590170207918774067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 351560557814241108900128357 65917604590170207918774067)
              ·
                refine ⟨98876406885255311878161101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65917604590170207918774067 98876406885255311878161101)
                ·
                  refine ⟨37078652581970741954310413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98876406885255311878161101 37078652581970741954310413)
                  ·
                    refine ⟨13904494718239028232866405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37078652581970741954310413 13904494718239028232866405)
                    ·
                      refine ⟨2607092759669817793662451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13904494718239028232866405 2607092759669817793662451)
                      ·
                        rfl

theorem cell23_5077295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_5077295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077295 prefixEnd_5077295 := by exact prefixLift 5077295
  have htrace : WordTrace (prefixWord ++ tailWord_5077295) baseStart_5077295 baseEnd_5077295 := by
    simpa [prefixWord, tailWord_5077295, baseEnd_5077295] using wordTrace_append hprefix tailTrace_5077295
  have hstable : (prefixWord ++ tailWord_5077295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077295).length < 2 ^ (prefixWord ++ tailWord_5077295).sum := by decide
  have hdescent : baseEnd_5077295 < baseStart_5077295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077312 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 3, 6, 2]
def baseStart_5077312 : Nat := 118140960795 + 5077312 * 2 ^ 59
def prefixEnd_5077312 : Nat := 4983230072969 + 3 ^ 40 * 5077312 * 2
def baseEnd_5077312 : Nat := 2607101488840944227149873

theorem tailTrace_5077312 : CollatzResearch.WordTrace tailWord_5077312 prefixEnd_5077312 2607101488840944227149873 := by
  unfold tailWord_5077312
  simp only [CollatzResearch.WordTrace]
  refine ⟨92592391090886617349249095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123456521454515489798998793 92592391090886617349249095)
  ·
    refine ⟨138888586636329926023873643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92592391090886617349249095 138888586636329926023873643)
    ·
      refine ⟨208332879954494889035810465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138888586636329926023873643 208332879954494889035810465)
      ·
        refine ⟨156249659965871166776857849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208332879954494889035810465 156249659965871166776857849)
        ·
          refine ⟨117187244974403375082643387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156249659965871166776857849 117187244974403375082643387)
          ·
            refine ⟨175780867461605062623965081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117187244974403375082643387 175780867461605062623965081)
            ·
              refine ⟨131835650596203796967973811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175780867461605062623965081 131835650596203796967973811)
              ·
                refine ⟨197753475894305695451960717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131835650596203796967973811 197753475894305695451960717)
                ·
                  refine ⟨74157553460364635794485269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197753475894305695451960717 74157553460364635794485269)
                  ·
                    refine ⟨3476135318454592302866497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74157553460364635794485269 3476135318454592302866497)
                    ·
                      refine ⟨2607101488840944227149873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476135318454592302866497 2607101488840944227149873)
                      ·
                        rfl

theorem cell23_5077312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_5077312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077312 prefixEnd_5077312 := by exact prefixLift 5077312
  have htrace : WordTrace (prefixWord ++ tailWord_5077312) baseStart_5077312 baseEnd_5077312 := by
    simpa [prefixWord, tailWord_5077312, baseEnd_5077312] using wordTrace_append hprefix tailTrace_5077312
  have hstable : (prefixWord ++ tailWord_5077312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077312).length < 2 ^ (prefixWord ++ tailWord_5077312).sum := by decide
  have hdescent : baseEnd_5077312 < baseStart_5077312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077346 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5077346 : Nat := 118140960795 + 5077346 * 2 ^ 59
def prefixEnd_5077346 : Nat := 4983230072969 + 3 ^ 40 * 5077346 * 2
def baseEnd_5077346 : Nat := 2607118947183197094124717

theorem tailTrace_5077346 : CollatzResearch.WordTrace tailWord_5077346 prefixEnd_5077346 2607118947183197094124717 := by
  unfold tailWord_5077346
  simp only [CollatzResearch.WordTrace]
  refine ⟨46296505565912514626308973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123457348175766705670157261 46296505565912514626308973)
  ·
    refine ⟨17361189587217192984865865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46296505565912514626308973 17361189587217192984865865)
    ·
      refine ⟨13020892190412894738649399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17361189587217192984865865 13020892190412894738649399)
      ·
        refine ⟨19531338285619342107974099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13020892190412894738649399 19531338285619342107974099)
        ·
          refine ⟨29297007428429013161961149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19531338285619342107974099 29297007428429013161961149)
          ·
            refine ⟨10986377785660879935735431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29297007428429013161961149 10986377785660879935735431)
            ·
              refine ⟨16479566678491319903603147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10986377785660879935735431 16479566678491319903603147)
              ·
                refine ⟨24719350017736979855404721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16479566678491319903603147 24719350017736979855404721)
                ·
                  refine ⟨18539512513302734891553541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24719350017736979855404721 18539512513302734891553541)
                  ·
                    refine ⟨3476158596244262792166289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18539512513302734891553541 3476158596244262792166289)
                    ·
                      refine ⟨2607118947183197094124717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476158596244262792166289 2607118947183197094124717)
                      ·
                        rfl

theorem cell23_5077346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5077346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077346 prefixEnd_5077346 := by exact prefixLift 5077346
  have htrace : WordTrace (prefixWord ++ tailWord_5077346) baseStart_5077346 baseEnd_5077346 := by
    simpa [prefixWord, tailWord_5077346, baseEnd_5077346] using wordTrace_append hprefix tailTrace_5077346
  have hstable : (prefixWord ++ tailWord_5077346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077346).length < 2 ^ (prefixWord ++ tailWord_5077346).sum := by decide
  have hdescent : baseEnd_5077346 < baseStart_5077346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077355 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6]
def baseStart_5077355 : Nat := 118140960795 + 5077355 * 2 ^ 59
def prefixEnd_5077355 : Nat := 4983230072969 + 3 ^ 40 * 5077355 * 2
def baseEnd_5077355 : Nat := 2607123568509087558912175

theorem tailTrace_5077355 : CollatzResearch.WordTrace tailWord_5077355 prefixEnd_5077355 2607123568509087558912175 := by
  unfold tailWord_5077355
  simp only [CollatzResearch.WordTrace]
  refine ⟨185186350520617453042313519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123457567013744968694875679 185186350520617453042313519)
  ·
    refine ⟨277779525780926179563470279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185186350520617453042313519 277779525780926179563470279)
    ·
      refine ⟨416669288671389269345205419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277779525780926179563470279 416669288671389269345205419)
      ·
        refine ⟨625003933007083904017808129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416669288671389269345205419 625003933007083904017808129)
        ·
          refine ⟨468752949755312928013356097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625003933007083904017808129 468752949755312928013356097)
          ·
            refine ⟨351564712316484696010017073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468752949755312928013356097 351564712316484696010017073)
            ·
              refine ⟨263673534237363522007512805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351564712316484696010017073 263673534237363522007512805)
              ·
                refine ⟨49438787669505660376408651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263673534237363522007512805 49438787669505660376408651)
                ·
                  refine ⟨74158181504258490564612977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49438787669505660376408651 74158181504258490564612977)
                  ·
                    refine ⟨55618636128193867923459733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74158181504258490564612977 55618636128193867923459733)
                    ·
                      refine ⟨2607123568509087558912175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55618636128193867923459733 2607123568509087558912175)
                      ·
                        rfl

theorem cell23_5077355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_5077355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077355 prefixEnd_5077355 := by exact prefixLift 5077355
  have htrace : WordTrace (prefixWord ++ tailWord_5077355) baseStart_5077355 baseEnd_5077355 := by
    simpa [prefixWord, tailWord_5077355, baseEnd_5077355] using wordTrace_append hprefix tailTrace_5077355
  have hstable : (prefixWord ++ tailWord_5077355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077355).length < 2 ^ (prefixWord ++ tailWord_5077355).sum := by decide
  have hdescent : baseEnd_5077355 < baseStart_5077355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077375 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_5077375 : Nat := 118140960795 + 5077375 * 2 ^ 59
def prefixEnd_5077375 : Nat := 4983230072969 + 3 ^ 40 * 5077375 * 2
def baseEnd_5077375 : Nat := 2607133838122177480662083

theorem tailTrace_5077375 : CollatzResearch.WordTrace tailWord_5077375 prefixEnd_5077375 2607133838122177480662083 := by
  unfold tailWord_5077375
  simp only [CollatzResearch.WordTrace]
  refine ⟨185187079980544996458041579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123458053320363330972027719 185187079980544996458041579)
  ·
    refine ⟨277780619970817494687062369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185187079980544996458041579 277780619970817494687062369)
    ·
      refine ⟨208335464978113121015296777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277780619970817494687062369 208335464978113121015296777)
      ·
        refine ⟨156251598733584840761472583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208335464978113121015296777 156251598733584840761472583)
        ·
          refine ⟨234377398100377261142208875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156251598733584840761472583 234377398100377261142208875)
          ·
            refine ⟨351566097150565891713313313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234377398100377261142208875 351566097150565891713313313)
            ·
              refine ⟨263674572862924418784984985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351566097150565891713313313 263674572862924418784984985)
              ·
                refine ⟨197755929647193314088738739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263674572862924418784984985 197755929647193314088738739)
                ·
                  refine ⟨296633894470789971133108109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197755929647193314088738739 296633894470789971133108109)
                  ·
                    refine ⟨111237710426546239174915541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296633894470789971133108109 111237710426546239174915541)
                    ·
                      refine ⟨2607133838122177480662083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111237710426546239174915541 2607133838122177480662083)
                      ·
                        rfl

theorem cell23_5077375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_5077375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077375 prefixEnd_5077375 := by exact prefixLift 5077375
  have htrace : WordTrace (prefixWord ++ tailWord_5077375) baseStart_5077375 baseEnd_5077375 := by
    simpa [prefixWord, tailWord_5077375, baseEnd_5077375] using wordTrace_append hprefix tailTrace_5077375
  have hstable : (prefixWord ++ tailWord_5077375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077375).length < 2 ^ (prefixWord ++ tailWord_5077375).sum := by decide
  have hdescent : baseEnd_5077375 < baseStart_5077375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077395 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 12]
def baseStart_5077395 : Nat := 118140960795 + 5077395 * 2 ^ 59
def prefixEnd_5077395 : Nat := 4983230072969 + 3 ^ 40 * 5077395 * 2
def baseEnd_5077395 : Nat := 869048035911755800803997

theorem tailTrace_5077395 : CollatzResearch.WordTrace tailWord_5077395 prefixEnd_5077395 869048035911755800803997 := by
  unfold tailWord_5077395
  simp only [CollatzResearch.WordTrace]
  refine ⟨185187809440472539873769639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123458539626981693249179759 185187809440472539873769639)
  ·
    refine ⟨277781714160708809810654459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185187809440472539873769639 277781714160708809810654459)
    ·
      refine ⟨416672571241063214715981689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277781714160708809810654459 416672571241063214715981689)
      ·
        refine ⟨312504428430797411036986267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416672571241063214715981689 312504428430797411036986267)
        ·
          refine ⟨468756642646196116555479401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312504428430797411036986267 468756642646196116555479401)
          ·
            refine ⟨351567481984647087416609551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468756642646196116555479401 351567481984647087416609551)
            ·
              refine ⟨527351222976970631124914327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351567481984647087416609551 527351222976970631124914327)
              ·
                refine ⟨791026834465455946687371491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527351222976970631124914327 791026834465455946687371491)
                ·
                  refine ⟨1186540251698183920031057237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791026834465455946687371491 1186540251698183920031057237)
                  ·
                    refine ⟨869048035911755800803997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1186540251698183920031057237 869048035911755800803997)
                    ·
                      rfl

theorem cell23_5077395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 12].length) (baseStart_5077395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077395 prefixEnd_5077395 := by exact prefixLift 5077395
  have htrace : WordTrace (prefixWord ++ tailWord_5077395) baseStart_5077395 baseEnd_5077395 := by
    simpa [prefixWord, tailWord_5077395, baseEnd_5077395] using wordTrace_append hprefix tailTrace_5077395
  have hstable : (prefixWord ++ tailWord_5077395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077395).length < 2 ^ (prefixWord ++ tailWord_5077395).sum := by decide
  have hdescent : baseEnd_5077395 < baseStart_5077395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077416 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5077416 : Nat := 118140960795 + 5077416 * 2 ^ 59
def prefixEnd_5077416 : Nat := 4983230072969 + 3 ^ 40 * 5077416 * 2
def baseEnd_5077416 : Nat := 869051630276337273416465

theorem tailTrace_5077416 : CollatzResearch.WordTrace tailWord_5077416 prefixEnd_5077416 869051630276337273416465 := by
  unfold tailWord_5077416
  simp only [CollatzResearch.WordTrace]
  refine ⟨92594287686698230230142051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123459050248930973640189401 92594287686698230230142051)
  ·
    refine ⟨138891431530047345345213077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92594287686698230230142051 138891431530047345345213077)
    ·
      refine ⟨6510535852970969313056863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138891431530047345345213077 6510535852970969313056863)
      ·
        refine ⟨9765803779456453969585295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510535852970969313056863 9765803779456453969585295)
        ·
          refine ⟨14648705669184680954377943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9765803779456453969585295 14648705669184680954377943)
          ·
            refine ⟨21973058503777021431566915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14648705669184680954377943 21973058503777021431566915)
            ·
              refine ⟨32959587755665532147350373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21973058503777021431566915 32959587755665532147350373)
              ·
                refine ⟨6179922704187287277628195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32959587755665532147350373 6179922704187287277628195)
                ·
                  refine ⟨9269884056280930916442293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179922704187287277628195 9269884056280930916442293)
                  ·
                    refine ⟨869051630276337273416465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9269884056280930916442293 869051630276337273416465)
                    ·
                      rfl

theorem cell23_5077416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5077416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077416 prefixEnd_5077416 := by exact prefixLift 5077416
  have htrace : WordTrace (prefixWord ++ tailWord_5077416) baseStart_5077416 baseEnd_5077416 := by
    simpa [prefixWord, tailWord_5077416, baseEnd_5077416] using wordTrace_append hprefix tailTrace_5077416
  have hstable : (prefixWord ++ tailWord_5077416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077416).length < 2 ^ (prefixWord ++ tailWord_5077416).sum := by decide
  have hdescent : baseEnd_5077416 < baseStart_5077416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077432 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_5077432 : Nat := 118140960795 + 5077432 * 2 ^ 59
def prefixEnd_5077432 : Nat := 4983230072969 + 3 ^ 40 * 5077432 * 2
def baseEnd_5077432 : Nat := 2607163106519483757649321

theorem tailTrace_5077432 : CollatzResearch.WordTrace tailWord_5077432 prefixEnd_5077432 2607163106519483757649321 := by
  unfold tailWord_5077432
  simp only [CollatzResearch.WordTrace]
  refine ⟨92594579470669247596433275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123459439294225663461911033 92594579470669247596433275)
  ·
    refine ⟨138891869206003871394649913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92594579470669247596433275 138891869206003871394649913)
    ·
      refine ⟨104168901904502903545987435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138891869206003871394649913 104168901904502903545987435)
      ·
        refine ⟨156253352856754355318981153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104168901904502903545987435 156253352856754355318981153)
        ·
          refine ⟨117190014642565766489235865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156253352856754355318981153 117190014642565766489235865)
          ·
            refine ⟨87892510981924324866926899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117190014642565766489235865 87892510981924324866926899)
            ·
              refine ⟨131838766472886487300390349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87892510981924324866926899 131838766472886487300390349)
              ·
                refine ⟨49439537427332432737646381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131838766472886487300390349 49439537427332432737646381)
                ·
                  refine ⟨18539826535249662276617393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49439537427332432737646381 18539826535249662276617393)
                  ·
                    refine ⟨13904869901437246707463045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18539826535249662276617393 13904869901437246707463045)
                    ·
                      refine ⟨2607163106519483757649321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13904869901437246707463045 2607163106519483757649321)
                      ·
                        rfl

theorem cell23_5077432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_5077432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077432 prefixEnd_5077432 := by exact prefixLift 5077432
  have htrace : WordTrace (prefixWord ++ tailWord_5077432) baseStart_5077432 baseEnd_5077432 := by
    simpa [prefixWord, tailWord_5077432, baseEnd_5077432] using wordTrace_append hprefix tailTrace_5077432
  have hstable : (prefixWord ++ tailWord_5077432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077432).length < 2 ^ (prefixWord ++ tailWord_5077432).sum := by decide
  have hdescent : baseEnd_5077432 < baseStart_5077432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077436 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_5077436 : Nat := 118140960795 + 5077436 * 2 ^ 59
def prefixEnd_5077436 : Nat := 4983230072969 + 3 ^ 40 * 5077436 * 2
def baseEnd_5077436 : Nat := 2607165160442101741999303

theorem tailTrace_5077436 : CollatzResearch.WordTrace tailWord_5077436 prefixEnd_5077436 2607165160442101741999303 := by
  unfold tailWord_5077436
  simp only [CollatzResearch.WordTrace]
  refine ⟨92594652416662001938006081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123459536555549335917341441 92594652416662001938006081)
  ·
    refine ⟨69445989312496501453504561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92594652416662001938006081 69445989312496501453504561)
    ·
      refine ⟨52084491984372376090128421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69445989312496501453504561 52084491984372376090128421)
      ·
        refine ⟨9765842247069820516899079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52084491984372376090128421 9765842247069820516899079)
        ·
          refine ⟨14648763370604730775348619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9765842247069820516899079 14648763370604730775348619)
          ·
            refine ⟨21973145055907096163022929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14648763370604730775348619 21973145055907096163022929)
            ·
              refine ⟨16479858791930322122267197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21973145055907096163022929 16479858791930322122267197)
              ·
                refine ⟨6179947046973870795850199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16479858791930322122267197 6179947046973870795850199)
                ·
                  refine ⟨9269920570460806193775299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179947046973870795850199 9269920570460806193775299)
                  ·
                    refine ⟨13904880855691209290662949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9269920570460806193775299 13904880855691209290662949)
                    ·
                      refine ⟨2607165160442101741999303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13904880855691209290662949 2607165160442101741999303)
                      ·
                        rfl

theorem cell23_5077436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_5077436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077436 prefixEnd_5077436 := by exact prefixLift 5077436
  have htrace : WordTrace (prefixWord ++ tailWord_5077436) baseStart_5077436 baseEnd_5077436 := by
    simpa [prefixWord, tailWord_5077436, baseEnd_5077436] using wordTrace_append hprefix tailTrace_5077436
  have hstable : (prefixWord ++ tailWord_5077436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077436).length < 2 ^ (prefixWord ++ tailWord_5077436).sum := by decide
  have hdescent : baseEnd_5077436 < baseStart_5077436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077486 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_5077486 : Nat := 118140960795 + 5077486 * 2 ^ 59
def prefixEnd_5077486 : Nat := 4983230072969 + 3 ^ 40 * 5077486 * 2
def baseEnd_5077486 : Nat := 2607190834474826546374073

theorem tailTrace_5077486 : CollatzResearch.WordTrace tailWord_5077486 prefixEnd_5077486 2607190834474826546374073 := by
  unfold tailWord_5077486
  simp only [CollatzResearch.WordTrace]
  refine ⟨23148891060392857801916539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123460752322095241610221541 23148891060392857801916539)
  ·
    refine ⟨34723336590589286702874809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23148891060392857801916539 34723336590589286702874809)
    ·
      refine ⟨26042502442941965027156107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34723336590589286702874809 26042502442941965027156107)
      ·
        refine ⟨39063753664412947540734161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26042502442941965027156107 39063753664412947540734161)
        ·
          refine ⟨29297815248309710655550621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39063753664412947540734161 29297815248309710655550621)
          ·
            refine ⟨10986680718116141495831483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29297815248309710655550621 10986680718116141495831483)
            ·
              refine ⟨16480021077174212243747225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10986680718116141495831483 16480021077174212243747225)
              ·
                refine ⟨12360015807880659182810419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16480021077174212243747225 12360015807880659182810419)
                ·
                  refine ⟨18540023711820988774215629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12360015807880659182810419 18540023711820988774215629)
                  ·
                    refine ⟨6952508891932870790330861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18540023711820988774215629 6952508891932870790330861)
                    ·
                      refine ⟨2607190834474826546374073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6952508891932870790330861 2607190834474826546374073)
                      ·
                        rfl

theorem cell23_5077486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_5077486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077486 prefixEnd_5077486 := by exact prefixLift 5077486
  have htrace : WordTrace (prefixWord ++ tailWord_5077486) baseStart_5077486 baseEnd_5077486 := by
    simpa [prefixWord, tailWord_5077486, baseEnd_5077486] using wordTrace_append hprefix tailTrace_5077486
  have hstable : (prefixWord ++ tailWord_5077486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077486).length < 2 ^ (prefixWord ++ tailWord_5077486).sum := by decide
  have hdescent : baseEnd_5077486 < baseStart_5077486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077490 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5077490 : Nat := 118140960795 + 5077490 * 2 ^ 59
def prefixEnd_5077490 : Nat := 4983230072969 + 3 ^ 40 * 5077490 * 2
def baseEnd_5077490 : Nat := 2607192888397444530724055

theorem tailTrace_5077490 : CollatzResearch.WordTrace tailWord_5077490 prefixEnd_5077490 2607192888397444530724055 := by
  unfold tailWord_5077490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46297818593782092774619481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123460849583418914065651949 46297818593782092774619481)
  ·
    refine ⟨34723363945336569580964611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46297818593782092774619481 34723363945336569580964611)
    ·
      refine ⟨52085045918004854371446917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34723363945336569580964611 52085045918004854371446917)
      ·
        refine ⟨9765946109625910194646297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52085045918004854371446917 9765946109625910194646297)
        ·
          refine ⟨7324459582219432645984723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9765946109625910194646297 7324459582219432645984723)
          ·
            refine ⟨10986689373329148968977085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7324459582219432645984723 10986689373329148968977085)
            ·
              refine ⟨4120008514998430863366407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10986689373329148968977085 4120008514998430863366407)
              ·
                refine ⟨6180012772497646295049611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120008514998430863366407 6180012772497646295049611)
                ·
                  refine ⟨9270019158746469442574417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180012772497646295049611 9270019158746469442574417)
                  ·
                    refine ⟨6952514369059852081930813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9270019158746469442574417 6952514369059852081930813)
                    ·
                      refine ⟨2607192888397444530724055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6952514369059852081930813 2607192888397444530724055)
                      ·
                        rfl

theorem cell23_5077490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5077490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077490 prefixEnd_5077490 := by exact prefixLift 5077490
  have htrace : WordTrace (prefixWord ++ tailWord_5077490) baseStart_5077490 baseEnd_5077490 := by
    simpa [prefixWord, tailWord_5077490, baseEnd_5077490] using wordTrace_append hprefix tailTrace_5077490
  have hstable : (prefixWord ++ tailWord_5077490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077490).length < 2 ^ (prefixWord ++ tailWord_5077490).sum := by decide
  have hdescent : baseEnd_5077490 < baseStart_5077490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077510 : List Nat := [6, 2, 1, 1, 1, 3, 1, 8]
def baseStart_5077510 : Nat := 118140960795 + 5077510 * 2 ^ 59
def prefixEnd_5077510 : Nat := 4983230072969 + 3 ^ 40 * 5077510 * 2
def baseEnd_5077510 : Nat := 96563079926316090832369

theorem tailTrace_5077510 : CollatzResearch.WordTrace tailWord_5077510 prefixEnd_5077510 96563079926316090832369 := by
  unfold tailWord_5077510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787250119845497328568937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123461335890037276342803989 5787250119845497328568937)
  ·
    refine ⟨4340437589884122996426703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5787250119845497328568937 4340437589884122996426703)
    ·
      refine ⟨6510656384826184494640055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340437589884122996426703 6510656384826184494640055)
      ·
        refine ⟨9765984577239276741960083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510656384826184494640055 9765984577239276741960083)
        ·
          refine ⟨14648976865858915112940125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9765984577239276741960083 14648976865858915112940125)
          ·
            refine ⟨5493366324697093167352547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14648976865858915112940125 5493366324697093167352547)
            ·
              refine ⟨8240049487045639751028821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5493366324697093167352547 8240049487045639751028821)
              ·
                refine ⟨96563079926316090832369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8240049487045639751028821 96563079926316090832369)
                ·
                  rfl

theorem cell23_5077510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_5077510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077510 prefixEnd_5077510 := by exact prefixLift 5077510
  have htrace : WordTrace (prefixWord ++ tailWord_5077510) baseStart_5077510 baseEnd_5077510 := by
    simpa [prefixWord, tailWord_5077510, baseEnd_5077510] using wordTrace_append hprefix tailTrace_5077510
  have hstable : (prefixWord ++ tailWord_5077510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077510).length < 2 ^ (prefixWord ++ tailWord_5077510).sum := by decide
  have hdescent : baseEnd_5077510 < baseStart_5077510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077559 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_5077559 : Nat := 118140960795 + 5077559 * 2 ^ 59
def prefixEnd_5077559 : Nat := 4983230072969 + 3 ^ 40 * 5077559 * 2
def baseEnd_5077559 : Nat := 2607228318562604760761237

theorem tailTrace_5077559 : CollatzResearch.WordTrace tailWord_5077559 prefixEnd_5077559 2607228318562604760761237 := by
  unfold tailWord_5077559
  simp only [CollatzResearch.WordTrace]
  refine ⟨185193791011878395882739731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123462527341252263921826487 185193791011878395882739731)
  ·
    refine ⟨277790686517817593824109597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185193791011878395882739731 277790686517817593824109597)
    ·
      refine ⟨104171507444181597684041099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277790686517817593824109597 104171507444181597684041099)
      ·
        refine ⟨156257261166272396526061649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104171507444181597684041099 156257261166272396526061649)
        ·
          refine ⟨117192945874704297394546237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156257261166272396526061649 117192945874704297394546237)
          ·
            refine ⟨43947354703014111522954839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117192945874704297394546237 43947354703014111522954839)
            ·
              refine ⟨65921032054521167284432259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43947354703014111522954839 65921032054521167284432259)
              ·
                refine ⟨98881548081781750926648389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65921032054521167284432259 98881548081781750926648389)
                ·
                  refine ⟨18540290265334078298746573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98881548081781750926648389 18540290265334078298746573)
                  ·
                    refine ⟨6952608849500279362029965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18540290265334078298746573 6952608849500279362029965)
                    ·
                      refine ⟨2607228318562604760761237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6952608849500279362029965 2607228318562604760761237)
                      ·
                        rfl

theorem cell23_5077559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_5077559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077559 prefixEnd_5077559 := by exact prefixLift 5077559
  have htrace : WordTrace (prefixWord ++ tailWord_5077559) baseStart_5077559 baseEnd_5077559 := by
    simpa [prefixWord, tailWord_5077559, baseEnd_5077559] using wordTrace_append hprefix tailTrace_5077559
  have hstable : (prefixWord ++ tailWord_5077559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077559).length < 2 ^ (prefixWord ++ tailWord_5077559).sum := by decide
  have hdescent : baseEnd_5077559 < baseStart_5077559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
