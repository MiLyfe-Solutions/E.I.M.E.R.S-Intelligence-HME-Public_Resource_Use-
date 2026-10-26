import V185TrunkScan23Chunk0321

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1903670 : List Nat := [5, 1, 2, 1, 1, 2, 3, 8]
def baseStart_1903670 : Nat := 118140960795 + 1903670 * 2 ^ 59
def prefixEnd_1903670 : Nat := 4983230072969 + 3 ^ 40 * 1903670 * 2
def baseEnd_1903670 : Nat := 36203619168321189484081

theorem tailTrace_1903670 : CollatzResearch.WordTrace tailWord_1903670 prefixEnd_1903670 36203619168321189484081 := by
  unfold tailWord_1903670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339534313333511612306779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46288366008890790531272309 4339534313333511612306779)
  ·
    refine ⟨6509301470000267418460169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4339534313333511612306779 6509301470000267418460169)
    ·
      refine ⟨4881976102500200563845127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6509301470000267418460169 4881976102500200563845127)
      ·
        refine ⟨7322964153750300845767691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881976102500200563845127 7322964153750300845767691)
        ·
          refine ⟨10984446230625451268651537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7322964153750300845767691 10984446230625451268651537)
          ·
            refine ⟨8238334672969088451488653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10984446230625451268651537 8238334672969088451488653)
            ·
              refine ⟨3089375502363408169308245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8238334672969088451488653 3089375502363408169308245)
              ·
                refine ⟨36203619168321189484081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3089375502363408169308245 36203619168321189484081)
                ·
                  rfl

theorem cell23_1903670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_1903670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903670 prefixEnd_1903670 := by exact prefixLift 1903670
  have htrace : WordTrace (prefixWord ++ tailWord_1903670) baseStart_1903670 baseEnd_1903670 := by
    simpa [prefixWord, tailWord_1903670, baseEnd_1903670] using wordTrace_append hprefix tailTrace_1903670
  have hstable : (prefixWord ++ tailWord_1903670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903670).length < 2 ^ (prefixWord ++ tailWord_1903670).sum := by decide
  have hdescent : baseEnd_1903670 < baseStart_1903670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903680 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3]
def baseStart_1903680 : Nat := 118140960795 + 1903680 * 2 ^ 59
def prefixEnd_1903680 : Nat := 4983230072969 + 3 ^ 40 * 1903680 * 2
def baseEnd_1903680 : Nat := 977502852351217076945141

theorem tailTrace_1903680 : CollatzResearch.WordTrace tailWord_1903680 prefixEnd_1903680 977502852351217076945141 := by
  unfold tailWord_1903680
  simp only [CollatzResearch.WordTrace]
  refine ⟨34716456871649978752386247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46288609162199971669848329 34716456871649978752386247)
  ·
    refine ⟨52074685307474968128579371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34716456871649978752386247 52074685307474968128579371)
    ·
      refine ⟨78112027961212452192869057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52074685307474968128579371 78112027961212452192869057)
      ·
        refine ⟨58584020970909339144651793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78112027961212452192869057 58584020970909339144651793)
        ·
          refine ⟨43938015728182004358488845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58584020970909339144651793 43938015728182004358488845)
          ·
            refine ⟨16476755898068251634433317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43938015728182004358488845 16476755898068251634433317)
            ·
              refine ⟨3089391730887797181456247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16476755898068251634433317 3089391730887797181456247)
              ·
                refine ⟨4634087596331695772184371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089391730887797181456247 4634087596331695772184371)
                ·
                  refine ⟨6951131394497543658276557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634087596331695772184371 6951131394497543658276557)
                  ·
                    refine ⟨2606674272936578871853709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6951131394497543658276557 2606674272936578871853709)
                    ·
                      refine ⟨977502852351217076945141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606674272936578871853709 977502852351217076945141)
                      ·
                        rfl

theorem cell23_1903680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_1903680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903680 prefixEnd_1903680 := by exact prefixLift 1903680
  have htrace : WordTrace (prefixWord ++ tailWord_1903680) baseStart_1903680 baseEnd_1903680 := by
    simpa [prefixWord, tailWord_1903680, baseEnd_1903680] using wordTrace_append hprefix tailTrace_1903680
  have hstable : (prefixWord ++ tailWord_1903680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903680).length < 2 ^ (prefixWord ++ tailWord_1903680).sum := by decide
  have hdescent : baseEnd_1903680 < baseStart_1903680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903713 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 2, 6]
def baseStart_1903713 : Nat := 118140960795 + 1903713 * 2 ^ 59
def prefixEnd_1903713 : Nat := 4983230072969 + 3 ^ 40 * 1903713 * 2
def baseEnd_1903713 : Nat := 325839932404271815944163

theorem tailTrace_1903713 : CollatzResearch.WordTrace tailWord_1903713 prefixEnd_1903713 325839932404271815944163 := by
  unfold tailWord_1903713
  simp only [CollatzResearch.WordTrace]
  refine ⟨69434117352180404140723793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46289411568120269427149195 69434117352180404140723793)
  ·
    refine ⟨52075588014135303105542845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69434117352180404140723793 52075588014135303105542845)
    ·
      refine ⟨19528345505300738664578567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52075588014135303105542845 19528345505300738664578567)
      ·
        refine ⟨29292518257951107996867851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19528345505300738664578567 29292518257951107996867851)
        ·
          refine ⟨43938777386926661995301777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29292518257951107996867851 43938777386926661995301777)
          ·
            refine ⟨32954083040194996496476333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43938777386926661995301777 32954083040194996496476333)
            ·
              refine ⟨12357781140073123686178625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32954083040194996496476333 12357781140073123686178625)
              ·
                refine ⟨9268335855054842764633969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12357781140073123686178625 9268335855054842764633969)
                ·
                  refine ⟨6951251891291132073475477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9268335855054842764633969 6951251891291132073475477)
                  ·
                    refine ⟨325839932404271815944163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6951251891291132073475477 325839932404271815944163)
                    ·
                      rfl

theorem cell23_1903713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_1903713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903713 prefixEnd_1903713 := by exact prefixLift 1903713
  have htrace : WordTrace (prefixWord ++ tailWord_1903713) baseStart_1903713 baseEnd_1903713 := by
    simpa [prefixWord, tailWord_1903713, baseEnd_1903713] using wordTrace_append hprefix tailTrace_1903713
  have hstable : (prefixWord ++ tailWord_1903713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903713).length < 2 ^ (prefixWord ++ tailWord_1903713).sum := by decide
  have hdescent : baseEnd_1903713 < baseStart_1903713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903714 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1903714 : Nat := 118140960795 + 1903714 * 2 ^ 59
def prefixEnd_1903714 : Nat := 4983230072969 + 3 ^ 40 * 1903714 * 2
def baseEnd_1903714 : Nat := 977520310693469943919985

theorem tailTrace_1903714 : CollatzResearch.WordTrace tailWord_1903714 prefixEnd_1903714 977520310693469943919985 := by
  unfold tailWord_1903714
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358538456294195327877549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46289435883451187541006797 17358538456294195327877549)
  ·
    refine ⟨6509451921110323247954081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17358538456294195327877549 6509451921110323247954081)
    ·
      refine ⟨4882088940832742435965561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6509451921110323247954081 4882088940832742435965561)
      ·
        refine ⟨3661566705624556826974171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4882088940832742435965561 3661566705624556826974171)
        ·
          refine ⟨5492350058436835240461257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661566705624556826974171 5492350058436835240461257)
          ·
            refine ⟨4119262543827626430345943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492350058436835240461257 4119262543827626430345943)
            ·
              refine ⟨6178893815741439645518915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119262543827626430345943 6178893815741439645518915)
              ·
                refine ⟨9268340723612159468278373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6178893815741439645518915 9268340723612159468278373)
                ·
                  refine ⟨1737813885677279900302195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9268340723612159468278373 1737813885677279900302195)
                  ·
                    refine ⟨2606720828515919850453293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737813885677279900302195 2606720828515919850453293)
                    ·
                      refine ⟨977520310693469943919985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606720828515919850453293 977520310693469943919985)
                      ·
                        rfl

theorem cell23_1903714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1903714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903714 prefixEnd_1903714 := by exact prefixLift 1903714
  have htrace : WordTrace (prefixWord ++ tailWord_1903714) baseStart_1903714 baseEnd_1903714 := by
    simpa [prefixWord, tailWord_1903714, baseEnd_1903714] using wordTrace_append hprefix tailTrace_1903714
  have hstable : (prefixWord ++ tailWord_1903714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903714).length < 2 ^ (prefixWord ++ tailWord_1903714).sum := by decide
  have hdescent : baseEnd_1903714 < baseStart_1903714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903760 : List Nat := [2, 1, 1, 1, 1, 1, 4, 7, 5]
def baseStart_1903760 : Nat := 118140960795 + 1903760 * 2 ^ 59
def prefixEnd_1903760 : Nat := 4983230072969 + 3 ^ 40 * 1903760 * 2
def baseEnd_1903760 : Nat := 108615992311508529327197

theorem tailTrace_1903760 : CollatzResearch.WordTrace tailWord_1903760 prefixEnd_1903760 108615992311508529327197 := by
  unfold tailWord_1903760
  simp only [CollatzResearch.WordTrace]
  refine ⟨34717915791505065583842367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46290554388673420778456489 34717915791505065583842367)
  ·
    refine ⟨52076873687257598375763551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34717915791505065583842367 52076873687257598375763551)
    ·
      refine ⟨78115310530886397563645327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52076873687257598375763551 78115310530886397563645327)
      ·
        refine ⟨117172965796329596345467991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78115310530886397563645327 117172965796329596345467991)
        ·
          refine ⟨175759448694494394518201987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117172965796329596345467991 175759448694494394518201987)
          ·
            refine ⟨263639173041741591777302981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175759448694494394518201987 263639173041741591777302981)
            ·
              refine ⟨49432344945326548458244309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263639173041741591777302981 49432344945326548458244309)
              ·
                refine ⟨1158570584656090979490101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49432344945326548458244309 1158570584656090979490101)
                ·
                  refine ⟨108615992311508529327197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1158570584656090979490101 108615992311508529327197)
                  ·
                    rfl

theorem cell23_1903760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 5].length) (baseStart_1903760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903760 prefixEnd_1903760 := by exact prefixLift 1903760
  have htrace : WordTrace (prefixWord ++ tailWord_1903760) baseStart_1903760 baseEnd_1903760 := by
    simpa [prefixWord, tailWord_1903760, baseEnd_1903760] using wordTrace_append hprefix tailTrace_1903760
  have hstable : (prefixWord ++ tailWord_1903760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903760).length < 2 ^ (prefixWord ++ tailWord_1903760).sum := by decide
  have hdescent : baseEnd_1903760 < baseStart_1903760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903828 : List Nat := [2, 4, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1903828 : Nat := 118140960795 + 1903828 * 2 ^ 59
def prefixEnd_1903828 : Nat := 4983230072969 + 3 ^ 40 * 1903828 * 2
def baseEnd_1903828 : Nat := 108619871943120277543829

theorem tailTrace_1903828 : CollatzResearch.WordTrace tailWord_1903828 prefixEnd_1903828 108619871943120277543829 := by
  unfold tailWord_1903828
  simp only [CollatzResearch.WordTrace]
  refine ⟨34719155873381889390580069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46292207831175852520773425 34719155873381889390580069)
  ·
    refine ⟨6509841726259104260733763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34719155873381889390580069 6509841726259104260733763)
    ·
      refine ⟨9764762589388656391100645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6509841726259104260733763 9764762589388656391100645)
      ·
        refine ⟨1830892985510373073331371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9764762589388656391100645 1830892985510373073331371)
        ·
          refine ⟨2746339478265559609997057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830892985510373073331371 2746339478265559609997057)
          ·
            refine ⟨2059754608699169707497793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746339478265559609997057 2059754608699169707497793)
            ·
              refine ⟨1544815956524377280623345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059754608699169707497793 1544815956524377280623345)
              ·
                refine ⟨1158611967393282960467509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544815956524377280623345 1158611967393282960467509)
                ·
                  refine ⟨108619871943120277543829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1158611967393282960467509 108619871943120277543829)
                  ·
                    rfl

theorem cell23_1903828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1903828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903828 prefixEnd_1903828 := by exact prefixLift 1903828
  have htrace : WordTrace (prefixWord ++ tailWord_1903828) baseStart_1903828 baseEnd_1903828 := by
    simpa [prefixWord, tailWord_1903828, baseEnd_1903828] using wordTrace_append hprefix tailTrace_1903828
  have hstable : (prefixWord ++ tailWord_1903828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903828).length < 2 ^ (prefixWord ++ tailWord_1903828).sum := by decide
  have hdescent : baseEnd_1903828 < baseStart_1903828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903877 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_1903877 : Nat := 118140960795 + 1903877 * 2 ^ 59
def prefixEnd_1903877 : Nat := 4983230072969 + 3 ^ 40 * 1903877 * 2
def baseEnd_1903877 : Nat := 977604008040152806181735

theorem tailTrace_1903877 : CollatzResearch.WordTrace tailWord_1903877 prefixEnd_1903877 977604008040152806181735 := by
  unfold tailWord_1903877
  simp only [CollatzResearch.WordTrace]
  refine ⟨69440098923586260149693885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46293399282390840099795923 69440098923586260149693885)
  ·
    refine ⟨26040037096344847556135207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69440098923586260149693885 26040037096344847556135207)
    ·
      refine ⟨39060055644517271334202811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26040037096344847556135207 39060055644517271334202811)
      ·
        refine ⟨58590083466775907001304217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39060055644517271334202811 58590083466775907001304217)
        ·
          refine ⟨43942562600081930250978163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58590083466775907001304217 43942562600081930250978163)
          ·
            refine ⟨65913843900122895376467245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43942562600081930250978163 65913843900122895376467245)
            ·
              refine ⟨24717691462546085766175217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65913843900122895376467245 24717691462546085766175217)
              ·
                refine ⟨18538268596909564324631413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24717691462546085766175217 18538268596909564324631413)
                ·
                  refine ⟨1737962680960271655434195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18538268596909564324631413 1737962680960271655434195)
                  ·
                    refine ⟨2606944021440407483151293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737962680960271655434195 2606944021440407483151293)
                    ·
                      refine ⟨977604008040152806181735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606944021440407483151293 977604008040152806181735)
                      ·
                        rfl

theorem cell23_1903877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_1903877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903877 prefixEnd_1903877 := by exact prefixLift 1903877
  have htrace : WordTrace (prefixWord ++ tailWord_1903877) baseStart_1903877 baseEnd_1903877 := by
    simpa [prefixWord, tailWord_1903877, baseEnd_1903877] using wordTrace_append hprefix tailTrace_1903877
  have hstable : (prefixWord ++ tailWord_1903877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903877).length < 2 ^ (prefixWord ++ tailWord_1903877).sum := by decide
  have hdescent : baseEnd_1903877 < baseStart_1903877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903914 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1903914 : Nat := 118140960795 + 1903914 * 2 ^ 59
def prefixEnd_1903914 : Nat := 4983230072969 + 3 ^ 40 * 1903914 * 2
def baseEnd_1903914 : Nat := 325874335608123053806355

theorem tailTrace_1903914 : CollatzResearch.WordTrace tailWord_1903914 prefixEnd_1903914 325874335608123053806355 := by
  unfold tailWord_1903914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17360362106113053867197699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46294298949634810312527197 17360362106113053867197699)
  ·
    refine ⟨26040543159169580800796549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17360362106113053867197699 26040543159169580800796549)
    ·
      refine ⟨4882601842344296400149353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26040543159169580800796549 4882601842344296400149353)
      ·
        refine ⟨3661951381758222300112015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4882601842344296400149353 3661951381758222300112015)
        ·
          refine ⟨5492927072637333450168023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661951381758222300112015 5492927072637333450168023)
          ·
            refine ⟨8239390608956000175252035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492927072637333450168023 8239390608956000175252035)
            ·
              refine ⟨12359085913434000262878053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8239390608956000175252035 12359085913434000262878053)
              ·
                refine ⟨2317328608768875049289635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12359085913434000262878053 2317328608768875049289635)
                ·
                  refine ⟨3475992913153312573934453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317328608768875049289635 3475992913153312573934453)
                  ·
                    refine ⟨325874335608123053806355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3475992913153312573934453 325874335608123053806355)
                    ·
                      rfl

theorem cell23_1903914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1903914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903914 prefixEnd_1903914 := by exact prefixLift 1903914
  have htrace : WordTrace (prefixWord ++ tailWord_1903914) baseStart_1903914 baseEnd_1903914 := by
    simpa [prefixWord, tailWord_1903914, baseEnd_1903914] using wordTrace_append hprefix tailTrace_1903914
  have hstable : (prefixWord ++ tailWord_1903914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903914).length < 2 ^ (prefixWord ++ tailWord_1903914).sum := by decide
  have hdescent : baseEnd_1903914 < baseStart_1903914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903920 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_1903920 : Nat := 118140960795 + 1903920 * 2 ^ 59
def prefixEnd_1903920 : Nat := 4983230072969 + 3 ^ 40 * 1903920 * 2
def baseEnd_1903920 : Nat := 977626087708296137944037

theorem tailTrace_1903920 : CollatzResearch.WordTrace tailWord_1903920 prefixEnd_1903920 977626087708296137944037 := by
  unfold tailWord_1903920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34720833631215239246754607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46294444841620318995672809 34720833631215239246754607)
  ·
    refine ⟨52081250446822858870131911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34720833631215239246754607 52081250446822858870131911)
    ·
      refine ⟨78121875670234288305197867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52081250446822858870131911 78121875670234288305197867)
      ·
        refine ⟨117182813505351432457796801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78121875670234288305197867 117182813505351432457796801)
        ·
          refine ⟨87887110129013574343347601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117182813505351432457796801 87887110129013574343347601)
          ·
            refine ⟨65915332596760180757510701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87887110129013574343347601 65915332596760180757510701)
            ·
              refine ⟨24718249723785067784066513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65915332596760180757510701 24718249723785067784066513)
              ·
                refine ⟨18538687292838800838049885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24718249723785067784066513 18538687292838800838049885)
                ·
                  refine ⟨6952007734814550314268707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18538687292838800838049885 6952007734814550314268707)
                  ·
                    refine ⟨10428011602221825471403061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952007734814550314268707 10428011602221825471403061)
                    ·
                      refine ⟨977626087708296137944037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10428011602221825471403061 977626087708296137944037)
                      ·
                        rfl

theorem cell23_1903920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_1903920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903920 prefixEnd_1903920 := by exact prefixLift 1903920
  have htrace : WordTrace (prefixWord ++ tailWord_1903920) baseStart_1903920 baseEnd_1903920 := by
    simpa [prefixWord, tailWord_1903920, baseEnd_1903920] using wordTrace_append hprefix tailTrace_1903920
  have hstable : (prefixWord ++ tailWord_1903920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903920).length < 2 ^ (prefixWord ++ tailWord_1903920).sum := by decide
  have hdescent : baseEnd_1903920 < baseStart_1903920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903934 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1903934 : Nat := 118140960795 + 1903934 * 2 ^ 59
def prefixEnd_1903934 : Nat := 4983230072969 + 3 ^ 40 * 1903934 * 2
def baseEnd_1903934 : Nat := 977633276437459083168973

theorem tailTrace_1903934 : CollatzResearch.WordTrace tailWord_1903934 prefixEnd_1903934 977633276437459083168973 := by
  unfold tailWord_1903934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680272235547469860564857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46294785256253172589679237 8680272235547469860564857)
  ·
    refine ⟨6510204176660602395423643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8680272235547469860564857 6510204176660602395423643)
    ·
      refine ⟨9765306264990903593135465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6510204176660602395423643 9765306264990903593135465)
      ·
        refine ⟨7323979698743177694851599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9765306264990903593135465 7323979698743177694851599)
        ·
          refine ⟨10985969548114766542277399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7323979698743177694851599 10985969548114766542277399)
          ·
            refine ⟨16478954322172149813416099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985969548114766542277399 16478954322172149813416099)
            ·
              refine ⟨24718431483258224720124149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16478954322172149813416099 24718431483258224720124149)
              ·
                refine ⟨2317352951555458567511639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24718431483258224720124149 2317352951555458567511639)
                ·
                  refine ⟨3476029427333187851267459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317352951555458567511639 3476029427333187851267459)
                  ·
                    refine ⟨5214044140999781776901189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3476029427333187851267459 5214044140999781776901189)
                    ·
                      refine ⟨977633276437459083168973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5214044140999781776901189 977633276437459083168973)
                      ·
                        rfl

theorem cell23_1903934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1903934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903934 prefixEnd_1903934 := by exact prefixLift 1903934
  have htrace : WordTrace (prefixWord ++ tailWord_1903934) baseStart_1903934 baseEnd_1903934 := by
    simpa [prefixWord, tailWord_1903934, baseEnd_1903934] using wordTrace_append hprefix tailTrace_1903934
  have hstable : (prefixWord ++ tailWord_1903934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903934).length < 2 ^ (prefixWord ++ tailWord_1903934).sum := by decide
  have hdescent : baseEnd_1903934 < baseStart_1903934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903957 : List Nat := [1, 3, 2, 2, 3, 2, 2, 8]
def baseStart_1903957 : Nat := 118140960795 + 1903957 * 2 ^ 59
def prefixEnd_1903957 : Nat := 4983230072969 + 3 ^ 40 * 1903957 * 2
def baseEnd_1903957 : Nat := 36209077277500462710421

theorem tailTrace_1903957 : CollatzResearch.WordTrace tailWord_1903957 prefixEnd_1903957 36209077277500462710421 := by
  unfold tailWord_1903957
  simp only [CollatzResearch.WordTrace]
  refine ⟨69443016763296433812606125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46295344508864289208404083 69443016763296433812606125)
  ·
    refine ⟨26041131286236162679727297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69443016763296433812606125 26041131286236162679727297)
    ·
      refine ⟨19530848464677122009795473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26041131286236162679727297 19530848464677122009795473)
      ·
        refine ⟨14648136348507841507346605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19530848464677122009795473 14648136348507841507346605)
        ·
          refine ⟨5493051130690440565254977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14648136348507841507346605 5493051130690440565254977)
          ·
            refine ⟨4119788348017830423941233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5493051130690440565254977 4119788348017830423941233)
            ·
              refine ⟨3089841261013372817955925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119788348017830423941233 3089841261013372817955925)
              ·
                refine ⟨36209077277500462710421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3089841261013372817955925 36209077277500462710421)
                ·
                  rfl

theorem cell23_1903957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 8].length) (baseStart_1903957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903957 prefixEnd_1903957 := by exact prefixLift 1903957
  have htrace : WordTrace (prefixWord ++ tailWord_1903957) baseStart_1903957 baseEnd_1903957 := by
    simpa [prefixWord, tailWord_1903957, baseEnd_1903957] using wordTrace_append hprefix tailTrace_1903957
  have hstable : (prefixWord ++ tailWord_1903957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903957).length < 2 ^ (prefixWord ++ tailWord_1903957).sum := by decide
  have hdescent : baseEnd_1903957 < baseStart_1903957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903960 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1903960 : Nat := 118140960795 + 1903960 * 2 ^ 59
def prefixEnd_1903960 : Nat := 4983230072969 + 3 ^ 40 * 1903960 * 2
def baseEnd_1903960 : Nat := 977646626934475981443853

theorem tailTrace_1903960 : CollatzResearch.WordTrace tailWord_1903960 prefixEnd_1903960 977646626934475981443853 := by
  unfold tailWord_1903960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34721563091142782662482667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46295417454857043549976889 34721563091142782662482667)
  ·
    refine ⟨52082344636714173993724001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34721563091142782662482667 52082344636714173993724001)
    ·
      refine ⟨39061758477535630495293001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52082344636714173993724001 39061758477535630495293001)
      ·
        refine ⟨29296318858151722871469751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39061758477535630495293001 29296318858151722871469751)
        ·
          refine ⟨43944478287227584307204627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29296318858151722871469751 43944478287227584307204627)
          ·
            refine ⟨65916717430841376460806941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43944478287227584307204627 65916717430841376460806941)
            ·
              refine ⟨24718769036565516172802603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65916717430841376460806941 24718769036565516172802603)
              ·
                refine ⟨37078153554848274259203905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24718769036565516172802603 37078153554848274259203905)
                ·
                  refine ⟨27808615166136205694402929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37078153554848274259203905 27808615166136205694402929)
                  ·
                    refine ⟨20856461374602154270802197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27808615166136205694402929 20856461374602154270802197)
                    ·
                      refine ⟨977646626934475981443853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20856461374602154270802197 977646626934475981443853)
                      ·
                        rfl

theorem cell23_1903960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1903960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903960 prefixEnd_1903960 := by exact prefixLift 1903960
  have htrace : WordTrace (prefixWord ++ tailWord_1903960) baseStart_1903960 baseEnd_1903960 := by
    simpa [prefixWord, tailWord_1903960, baseEnd_1903960] using wordTrace_append hprefix tailTrace_1903960
  have hstable : (prefixWord ++ tailWord_1903960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903960).length < 2 ^ (prefixWord ++ tailWord_1903960).sum := by decide
  have hdescent : baseEnd_1903960 < baseStart_1903960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903965 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1903965 : Nat := 118140960795 + 1903965 * 2 ^ 59
def prefixEnd_1903965 : Nat := 4983230072969 + 3 ^ 40 * 1903965 * 2
def baseEnd_1903965 : Nat := 325883064779249487293777

theorem tailTrace_1903965 : CollatzResearch.WordTrace tailWord_1903965 prefixEnd_1903965 325883064779249487293777 := by
  unfold tailWord_1903965
  simp only [CollatzResearch.WordTrace]
  refine ⟨69443308547267451178897349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46295539031511634119264899 69443308547267451178897349)
  ·
    refine ⟨13020620352612647096043253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69443308547267451178897349 13020620352612647096043253)
    ·
      refine ⟨1220683158057435665254055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13020620352612647096043253 1220683158057435665254055)
      ·
        refine ⟨1831024737086153497881083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220683158057435665254055 1831024737086153497881083)
        ·
          refine ⟨2746537105629230246821625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831024737086153497881083 2746537105629230246821625)
          ·
            refine ⟨2059902829221922685116219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746537105629230246821625 2059902829221922685116219)
            ·
              refine ⟨3089854243832884027674329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059902829221922685116219 3089854243832884027674329)
              ·
                refine ⟨2317390682874663020755747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089854243832884027674329 2317390682874663020755747)
                ·
                  refine ⟨3476086024311994531133621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317390682874663020755747 3476086024311994531133621)
                  ·
                    refine ⟨325883064779249487293777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3476086024311994531133621 325883064779249487293777)
                    ·
                      rfl

theorem cell23_1903965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1903965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903965 prefixEnd_1903965 := by exact prefixLift 1903965
  have htrace : WordTrace (prefixWord ++ tailWord_1903965) baseStart_1903965 baseEnd_1903965 := by
    simpa [prefixWord, tailWord_1903965, baseEnd_1903965] using wordTrace_append hprefix tailTrace_1903965
  have hstable : (prefixWord ++ tailWord_1903965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903965).length < 2 ^ (prefixWord ++ tailWord_1903965).sum := by decide
  have hdescent : baseEnd_1903965 < baseStart_1903965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903967 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 3]
def baseStart_1903967 : Nat := 118140960795 + 1903967 * 2 ^ 59
def prefixEnd_1903967 : Nat := 4983230072969 + 3 ^ 40 * 1903967 * 2
def baseEnd_1903967 : Nat := 977650221299057454056321

theorem tailTrace_1903967 : CollatzResearch.WordTrace tailWord_1903967 prefixEnd_1903967 977650221299057454056321 := by
  unfold tailWord_1903967
  simp only [CollatzResearch.WordTrace]
  refine ⟨69443381493260205520470155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46295587662173470346980103 69443381493260205520470155)
  ·
    refine ⟨104165072239890308280705233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69443381493260205520470155 104165072239890308280705233)
    ·
      refine ⟨78123804179917731210528925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104165072239890308280705233 78123804179917731210528925)
      ·
        refine ⟨29296426567469149203948347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78123804179917731210528925 29296426567469149203948347)
        ·
          refine ⟨43944639851203723805922521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29296426567469149203948347 43944639851203723805922521)
          ·
            refine ⟨32958479888402792854441891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43944639851203723805922521 32958479888402792854441891)
            ·
              refine ⟨49437719832604189281662837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32958479888402792854441891 49437719832604189281662837)
              ·
                refine ⟨4634786234306642745155891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49437719832604189281662837 4634786234306642745155891)
                ·
                  refine ⟨6952179351459964117733837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634786234306642745155891 6952179351459964117733837)
                  ·
                    refine ⟨2607067256797486544150189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6952179351459964117733837 2607067256797486544150189)
                    ·
                      refine ⟨977650221299057454056321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607067256797486544150189 977650221299057454056321)
                      ·
                        rfl

theorem cell23_1903967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_1903967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903967 prefixEnd_1903967 := by exact prefixLift 1903967
  have htrace : WordTrace (prefixWord ++ tailWord_1903967) baseStart_1903967 baseEnd_1903967 := by
    simpa [prefixWord, tailWord_1903967, baseEnd_1903967] using wordTrace_append hprefix tailTrace_1903967
  have hstable : (prefixWord ++ tailWord_1903967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903967).length < 2 ^ (prefixWord ++ tailWord_1903967).sum := by decide
  have hdescent : baseEnd_1903967 < baseStart_1903967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903971 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1903971 : Nat := 118140960795 + 1903971 * 2 ^ 59
def prefixEnd_1903971 : Nat := 4983230072969 + 3 ^ 40 * 1903971 * 2
def baseEnd_1903971 : Nat := 977652275221675438406303

theorem tailTrace_1903971 : CollatzResearch.WordTrace tailWord_1903971 prefixEnd_1903971 977652275221675438406303 := by
  unfold tailWord_1903971
  simp only [CollatzResearch.WordTrace]
  refine ⟨69443527385245714203615767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46295684923497142802410511 69443527385245714203615767)
  ·
    refine ⟨104165291077868571305423651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69443527385245714203615767 104165291077868571305423651)
    ·
      refine ⟨156247936616802856958135477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104165291077868571305423651 156247936616802856958135477)
      ·
        refine ⟨14648244057825267839825201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156247936616802856958135477 14648244057825267839825201)
        ·
          refine ⟨10986183043368950879868901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14648244057825267839825201 10986183043368950879868901)
          ·
            refine ⟨2059909320631678289975419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10986183043368950879868901 2059909320631678289975419)
            ·
              refine ⟨3089863980947517434963129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059909320631678289975419 3089863980947517434963129)
              ·
                refine ⟨2317397985710638076222347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089863980947517434963129 2317397985710638076222347)
                ·
                  refine ⟨3476096978565957114333521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317397985710638076222347 3476096978565957114333521)
                  ·
                    refine ⟨2607072733924467835750141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3476096978565957114333521 2607072733924467835750141)
                    ·
                      refine ⟨977652275221675438406303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607072733924467835750141 977652275221675438406303)
                      ·
                        rfl

theorem cell23_1903971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1903971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903971 prefixEnd_1903971 := by exact prefixLift 1903971
  have htrace : WordTrace (prefixWord ++ tailWord_1903971) baseStart_1903971 baseEnd_1903971 := by
    simpa [prefixWord, tailWord_1903971, baseEnd_1903971] using wordTrace_append hprefix tailTrace_1903971
  have hstable : (prefixWord ++ tailWord_1903971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903971).length < 2 ^ (prefixWord ++ tailWord_1903971).sum := by decide
  have hdescent : baseEnd_1903971 < baseStart_1903971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904000 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 3, 8]
def baseStart_1904000 : Nat := 118140960795 + 1904000 * 2 ^ 59
def prefixEnd_1904000 : Nat := 4983230072969 + 3 ^ 40 * 1904000 * 2
def baseEnd_1904000 : Nat := 325889055386885274981223

theorem tailTrace_1904000 : CollatzResearch.WordTrace tailWord_1904000 prefixEnd_1904000 325889055386885274981223 := by
  unfold tailWord_1904000
  simp only [CollatzResearch.WordTrace]
  refine ⟨34722292551070326078210727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46296390068093768104280969 34722292551070326078210727)
  ·
    refine ⟨52083438826605489117316091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34722292551070326078210727 52083438826605489117316091)
    ·
      refine ⟨78125158239908233675974137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52083438826605489117316091 78125158239908233675974137)
      ·
        refine ⟨58593868679931175256980603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78125158239908233675974137 58593868679931175256980603)
        ·
          refine ⟨87890803019896762885470905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58593868679931175256980603 87890803019896762885470905)
          ·
            refine ⟨65918102264922572164103179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87890803019896762885470905 65918102264922572164103179)
            ·
              refine ⟨98877153397383858246154769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65918102264922572164103179 98877153397383858246154769)
              ·
                refine ⟨74157865048037893684616077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98877153397383858246154769 74157865048037893684616077)
                ·
                  refine ⟨27809199393014210131731029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74157865048037893684616077 27809199393014210131731029)
                  ·
                    refine ⟨325889055386885274981223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27809199393014210131731029 325889055386885274981223)
                    ·
                      rfl

theorem cell23_1904000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_1904000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904000 prefixEnd_1904000 := by exact prefixLift 1904000
  have htrace : WordTrace (prefixWord ++ tailWord_1904000) baseStart_1904000 baseEnd_1904000 := by
    simpa [prefixWord, tailWord_1904000, baseEnd_1904000] using wordTrace_append hprefix tailTrace_1904000
  have hstable : (prefixWord ++ tailWord_1904000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904000).length < 2 ^ (prefixWord ++ tailWord_1904000).sum := by decide
  have hdescent : baseEnd_1904000 < baseStart_1904000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904002 : List Nat := [3, 4, 2, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_1904002 : Nat := 118140960795 + 1904002 * 2 ^ 59
def prefixEnd_1904002 : Nat := 4983230072969 + 3 ^ 40 * 1904002 * 2
def baseEnd_1904002 : Nat := 977668193121964817118661

theorem tailTrace_1904002 : CollatzResearch.WordTrace tailWord_1904002 prefixEnd_1904002 977668193121964817118661 := by
  unfold tailWord_1904002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17361164512033351624498565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46296438698755604331996173 17361164512033351624498565)
  ·
    refine ⟨3255218346006253429593481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17361164512033351624498565 3255218346006253429593481)
    ·
      refine ⟨2441413759504690072195111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3255218346006253429593481 2441413759504690072195111)
      ·
        refine ⟨3662120639257035108292667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441413759504690072195111 3662120639257035108292667)
        ·
          refine ⟨5493180958885552662439001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3662120639257035108292667 5493180958885552662439001)
          ·
            refine ⟨4119885719164164496829251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5493180958885552662439001 4119885719164164496829251)
            ·
              refine ⟨6179828578746246745243877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119885719164164496829251 6179828578746246745243877)
              ·
                refine ⟨1158717858514921264733227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6179828578746246745243877 1158717858514921264733227)
                ·
                  refine ⟨1738076787772381897099841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158717858514921264733227 1738076787772381897099841)
                  ·
                    refine ⟨1303557590829286422824881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738076787772381897099841 1303557590829286422824881)
                    ·
                      refine ⟨977668193121964817118661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303557590829286422824881 977668193121964817118661)
                      ·
                        rfl

theorem cell23_1904002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_1904002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904002 prefixEnd_1904002 := by exact prefixLift 1904002
  have htrace : WordTrace (prefixWord ++ tailWord_1904002) baseStart_1904002 baseEnd_1904002 := by
    simpa [prefixWord, tailWord_1904002, baseEnd_1904002] using wordTrace_append hprefix tailTrace_1904002
  have hstable : (prefixWord ++ tailWord_1904002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904002).length < 2 ^ (prefixWord ++ tailWord_1904002).sum := by decide
  have hdescent : baseEnd_1904002 < baseStart_1904002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904007 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1904007 : Nat := 118140960795 + 1904007 * 2 ^ 59
def prefixEnd_1904007 : Nat := 4983230072969 + 3 ^ 40 * 1904007 * 2
def baseEnd_1904007 : Nat := 977670760525237297556137

theorem tailTrace_1904007 : CollatzResearch.WordTrace tailWord_1904007 prefixEnd_1904007 977670760525237297556137 := by
  unfold tailWord_1904007
  simp only [CollatzResearch.WordTrace]
  refine ⟨69444840413115292351926275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46296560275410194901284183 69444840413115292351926275)
  ·
    refine ⟨104167260619672938527889413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69444840413115292351926275 104167260619672938527889413)
    ·
      refine ⟨19531361366188675973979265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104167260619672938527889413 19531361366188675973979265)
      ·
        refine ⟨14648521024641506980484449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19531361366188675973979265 14648521024641506980484449)
        ·
          refine ⟨10986390768481130235363337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14648521024641506980484449 10986390768481130235363337)
          ·
            refine ⟨8239793076360847676522503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10986390768481130235363337 8239793076360847676522503)
            ·
              refine ⟨12359689614541271514783755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8239793076360847676522503 12359689614541271514783755)
              ·
                refine ⟨18539534421811907272175633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12359689614541271514783755 18539534421811907272175633)
                ·
                  refine ⟨13904650816358930454131725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18539534421811907272175633 13904650816358930454131725)
                  ·
                    refine ⟨5214244056134598920299397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13904650816358930454131725 5214244056134598920299397)
                    ·
                      refine ⟨977670760525237297556137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5214244056134598920299397 977670760525237297556137)
                      ·
                        rfl

theorem cell23_1904007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1904007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904007 prefixEnd_1904007 := by exact prefixLift 1904007
  have htrace : WordTrace (prefixWord ++ tailWord_1904007) baseStart_1904007 baseEnd_1904007 := by
    simpa [prefixWord, tailWord_1904007, baseEnd_1904007] using wordTrace_append hprefix tailTrace_1904007
  have hstable : (prefixWord ++ tailWord_1904007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904007).length < 2 ^ (prefixWord ++ tailWord_1904007).sum := by decide
  have hdescent : baseEnd_1904007 < baseStart_1904007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904018 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1904018 : Nat := 118140960795 + 1904018 * 2 ^ 59
def prefixEnd_1904018 : Nat := 4983230072969 + 3 ^ 40 * 1904018 * 2
def baseEnd_1904018 : Nat := 977676408812436754518587

theorem tailTrace_1904018 : CollatzResearch.WordTrace tailWord_1904018 prefixEnd_1904018 977676408812436754518587 := by
  unfold tailWord_1904018
  simp only [CollatzResearch.WordTrace]
  refine ⟨17361310404018860307644177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46296827744050294153717805 17361310404018860307644177)
  ·
    refine ⟨13020982803014145230733133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17361310404018860307644177 13020982803014145230733133)
    ·
      refine ⟨4882868551130304461524925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13020982803014145230733133 4882868551130304461524925)
      ·
        refine ⟨1831075706673864173071847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4882868551130304461524925 1831075706673864173071847)
        ·
          refine ⟨2746613560010796259607771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831075706673864173071847 2746613560010796259607771)
          ·
            refine ⟨4119920340016194389411657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746613560010796259607771 4119920340016194389411657)
            ·
              refine ⟨3089940255012145792058743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119920340016194389411657 3089940255012145792058743)
              ·
                refine ⟨4634910382518218688088115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089940255012145792058743 4634910382518218688088115)
                ·
                  refine ⟨6952365573777328032132173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634910382518218688088115 6952365573777328032132173)
                  ·
                    refine ⟨2607137090166498012049565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6952365573777328032132173 2607137090166498012049565)
                    ·
                      refine ⟨977676408812436754518587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607137090166498012049565 977676408812436754518587)
                      ·
                        rfl

theorem cell23_1904018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1904018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904018 prefixEnd_1904018 := by exact prefixLift 1904018
  have htrace : WordTrace (prefixWord ++ tailWord_1904018) baseStart_1904018 baseEnd_1904018 := by
    simpa [prefixWord, tailWord_1904018, baseEnd_1904018] using wordTrace_append hprefix tailTrace_1904018
  have hstable : (prefixWord ++ tailWord_1904018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904018).length < 2 ^ (prefixWord ++ tailWord_1904018).sum := by decide
  have hdescent : baseEnd_1904018 < baseStart_1904018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904045 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_1904045 : Nat := 118140960795 + 1904045 * 2 ^ 59
def prefixEnd_1904045 : Nat := 4983230072969 + 3 ^ 40 * 1904045 * 2
def baseEnd_1904045 : Nat := 977690272790108148880963

theorem tailTrace_1904045 : CollatzResearch.WordTrace tailWord_1904045 prefixEnd_1904045 977690272790108148880963 := by
  unfold tailWord_1904045
  simp only [CollatzResearch.WordTrace]
  refine ⟨69446226386977624841809589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46297484257985083227873059 69446226386977624841809589)
  ·
    refine ⟨6510583723779152328919649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69446226386977624841809589 6510583723779152328919649)
    ·
      refine ⟨4882937792834364246689737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6510583723779152328919649 4882937792834364246689737)
      ·
        refine ⟨3662203344625773185017303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4882937792834364246689737 3662203344625773185017303)
        ·
          refine ⟨5493305016938659777525955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3662203344625773185017303 5493305016938659777525955)
          ·
            refine ⟨8239957525407989666288933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493305016938659777525955 8239957525407989666288933)
            ·
              refine ⟨1544992036013998062429175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8239957525407989666288933 1544992036013998062429175)
              ·
                refine ⟨2317488054020997093643763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544992036013998062429175 2317488054020997093643763)
                ·
                  refine ⟨3476232081031495640465645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317488054020997093643763 3476232081031495640465645)
                  ·
                    refine ⟨1303587030386810865174617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3476232081031495640465645 1303587030386810865174617)
                    ·
                      refine ⟨977690272790108148880963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303587030386810865174617 977690272790108148880963)
                      ·
                        rfl

theorem cell23_1904045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_1904045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904045 prefixEnd_1904045 := by exact prefixLift 1904045
  have htrace : WordTrace (prefixWord ++ tailWord_1904045) baseStart_1904045 baseEnd_1904045 := by
    simpa [prefixWord, tailWord_1904045, baseEnd_1904045] using wordTrace_append hprefix tailTrace_1904045
  have hstable : (prefixWord ++ tailWord_1904045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904045).length < 2 ^ (prefixWord ++ tailWord_1904045).sum := by decide
  have hdescent : baseEnd_1904045 < baseStart_1904045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904064 : List Nat := [2, 1, 1, 2, 3, 1, 4, 4, 5]
def baseStart_1904064 : Nat := 118140960795 + 1904064 * 2 ^ 59
def prefixEnd_1904064 : Nat := 4983230072969 + 3 ^ 40 * 1904064 * 2
def baseEnd_1904064 : Nat := 108633336546949286060375

theorem tailTrace_1904064 : CollatzResearch.WordTrace tailWord_1904064 prefixEnd_1904064 108633336546949286060375 := by
  unfold tailWord_1904064
  simp only [CollatzResearch.WordTrace]
  refine ⟨34723459686954395543375623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46297946249272527391167497 34723459686954395543375623)
  ·
    refine ⟨52085189530431593315063435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34723459686954395543375623 52085189530431593315063435)
    ·
      refine ⟨78127784295647389972595153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52085189530431593315063435 78127784295647389972595153)
      ·
        refine ⟨58595838221735542479446365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78127784295647389972595153 58595838221735542479446365)
        ·
          refine ⟨21973439333150828429792387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58595838221735542479446365 21973439333150828429792387)
          ·
            refine ⟨32960158999726242644688581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21973439333150828429792387 32960158999726242644688581)
            ·
              refine ⟨6180029812448670495879109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32960158999726242644688581 6180029812448670495879109)
              ·
                refine ⟨1158755589834125717977333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6180029812448670495879109 1158755589834125717977333)
                ·
                  refine ⟨108633336546949286060375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1158755589834125717977333 108633336546949286060375)
                  ·
                    rfl

theorem cell23_1904064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 5].length) (baseStart_1904064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904064 prefixEnd_1904064 := by exact prefixLift 1904064
  have htrace : WordTrace (prefixWord ++ tailWord_1904064) baseStart_1904064 baseEnd_1904064 := by
    simpa [prefixWord, tailWord_1904064, baseEnd_1904064] using wordTrace_append hprefix tailTrace_1904064
  have hstable : (prefixWord ++ tailWord_1904064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904064).length < 2 ^ (prefixWord ++ tailWord_1904064).sum := by decide
  have hdescent : baseEnd_1904064 < baseStart_1904064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904074 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_1904074 : Nat := 118140960795 + 1904074 * 2 ^ 59
def prefixEnd_1904074 : Nat := 4983230072969 + 3 ^ 40 * 1904074 * 2
def baseEnd_1904074 : Nat := 977705163729088535418329

theorem tailTrace_1904074 : CollatzResearch.WordTrace tailWord_1904074 prefixEnd_1904074 977705163729088535418329 := by
  unfold tailWord_1904074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17361821025968140698653819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46298189402581708529743517 17361821025968140698653819)
  ·
    refine ⟨26042731538952211047980729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17361821025968140698653819 26042731538952211047980729)
    ·
      refine ⟨19532048654214158285985547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26042731538952211047980729 19532048654214158285985547)
      ·
        refine ⟨29298072981321237428978321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532048654214158285985547 29298072981321237428978321)
        ·
          refine ⟨21973554735990928071733741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29298072981321237428978321 21973554735990928071733741)
          ·
            refine ⟨8240083025996598026900153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21973554735990928071733741 8240083025996598026900153)
            ·
              refine ⟨6180062269497448520175115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8240083025996598026900153 6180062269497448520175115)
              ·
                refine ⟨9270093404246172780262673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180062269497448520175115 9270093404246172780262673)
                ·
                  refine ⟨6952570053184629585197005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9270093404246172780262673 6952570053184629585197005)
                  ·
                    refine ⟨2607213769944236094448877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6952570053184629585197005 2607213769944236094448877)
                    ·
                      refine ⟨977705163729088535418329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607213769944236094448877 977705163729088535418329)
                      ·
                        rfl

theorem cell23_1904074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_1904074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904074 prefixEnd_1904074 := by exact prefixLift 1904074
  have htrace : WordTrace (prefixWord ++ tailWord_1904074) baseStart_1904074 baseEnd_1904074 := by
    simpa [prefixWord, tailWord_1904074, baseEnd_1904074] using wordTrace_append hprefix tailTrace_1904074
  have hstable : (prefixWord ++ tailWord_1904074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904074).length < 2 ^ (prefixWord ++ tailWord_1904074).sum := by decide
  have hdescent : baseEnd_1904074 < baseStart_1904074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904126 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1904126 : Nat := 118140960795 + 1904126 * 2 ^ 59
def prefixEnd_1904126 : Nat := 4983230072969 + 3 ^ 40 * 1904126 * 2
def baseEnd_1904126 : Nat := 977731864723122331968091

theorem tailTrace_1904126 : CollatzResearch.WordTrace tailWord_1904126 prefixEnd_1904126 977731864723122331968091 := by
  unfold tailWord_1904126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681147587460521959438529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46299453799789450450338821 8681147587460521959438529)
  ·
    refine ⟨6510860690595391469578897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8681147587460521959438529 6510860690595391469578897)
    ·
      refine ⟨4883145517946543602184173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6510860690595391469578897 4883145517946543602184173)
      ·
        refine ⟨1831179569229953850819065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4883145517946543602184173 1831179569229953850819065)
        ·
          refine ⟨1373384676922465388114299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831179569229953850819065 1373384676922465388114299)
          ·
            refine ⟨2060077015383698082171449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373384676922465388114299 2060077015383698082171449)
            ·
              refine ⟨1545057761537773561628587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060077015383698082171449 1545057761537773561628587)
              ·
                refine ⟨2317586642306660342442881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545057761537773561628587 2317586642306660342442881)
                ·
                  refine ⟨1738189981729995256832161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2317586642306660342442881 1738189981729995256832161)
                  ·
                    refine ⟨1303642486297496442624121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738189981729995256832161 1303642486297496442624121)
                    ·
                      refine ⟨977731864723122331968091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303642486297496442624121 977731864723122331968091)
                      ·
                        rfl

theorem cell23_1904126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1904126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904126 prefixEnd_1904126 := by exact prefixLift 1904126
  have htrace : WordTrace (prefixWord ++ tailWord_1904126) baseStart_1904126 baseEnd_1904126 := by
    simpa [prefixWord, tailWord_1904126, baseEnd_1904126] using wordTrace_append hprefix tailTrace_1904126
  have hstable : (prefixWord ++ tailWord_1904126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904126).length < 2 ^ (prefixWord ++ tailWord_1904126).sum := by decide
  have hdescent : baseEnd_1904126 < baseStart_1904126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904127 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_1904127 : Nat := 118140960795 + 1904127 * 2 ^ 59
def prefixEnd_1904127 : Nat := 4983230072969 + 3 ^ 40 * 1904127 * 2
def baseEnd_1904127 : Nat := 977732378203776828055585

theorem tailTrace_1904127 : CollatzResearch.WordTrace tailWord_1904127 prefixEnd_1904127 977732378203776828055585 := by
  unfold tailWord_1904127
  simp only [CollatzResearch.WordTrace]
  refine ⟨69449217172680552846294635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46299478115120368564196423 69449217172680552846294635)
  ·
    refine ⟨104173825759020829269441953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69449217172680552846294635 104173825759020829269441953)
    ·
      refine ⟨78130369319265621952081465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104173825759020829269441953 78130369319265621952081465)
      ·
        refine ⟨58597776989449216464061099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78130369319265621952081465 58597776989449216464061099)
        ·
          refine ⟨87896665484173824696091649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58597776989449216464061099 87896665484173824696091649)
          ·
            refine ⟨65922499113130368522068737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87896665484173824696091649 65922499113130368522068737)
            ·
              refine ⟨49441874334847776391551553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65922499113130368522068737 49441874334847776391551553)
              ·
                refine ⟨37081405751135832293663665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49441874334847776391551553 37081405751135832293663665)
                ·
                  refine ⟨27811054313351874220247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37081405751135832293663665 27811054313351874220247749)
                  ·
                    refine ⟨5214572683753476416296453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27811054313351874220247749 5214572683753476416296453)
                    ·
                      refine ⟨977732378203776828055585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5214572683753476416296453 977732378203776828055585)
                      ·
                        rfl

theorem cell23_1904127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_1904127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904127 prefixEnd_1904127 := by exact prefixLift 1904127
  have htrace : WordTrace (prefixWord ++ tailWord_1904127) baseStart_1904127 baseEnd_1904127 := by
    simpa [prefixWord, tailWord_1904127, baseEnd_1904127] using wordTrace_append hprefix tailTrace_1904127
  have hstable : (prefixWord ++ tailWord_1904127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904127).length < 2 ^ (prefixWord ++ tailWord_1904127).sum := by decide
  have hdescent : baseEnd_1904127 < baseStart_1904127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904184 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 3, 5]
def baseStart_1904184 : Nat := 118140960795 + 1904184 * 2 ^ 59
def prefixEnd_1904184 : Nat := 4983230072969 + 3 ^ 40 * 1904184 * 2
def baseEnd_1904184 : Nat := 325920548867027701680941

theorem tailTrace_1904184 : CollatzResearch.WordTrace tailWord_1904184 prefixEnd_1904184 325920548867027701680941 := by
  unfold tailWord_1904184
  simp only [CollatzResearch.WordTrace]
  refine ⟨34725648066737025790559803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46300864088982701054079737 34725648066737025790559803)
  ·
    refine ⟨52088472100105538685839705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34725648066737025790559803 52088472100105538685839705)
    ·
      refine ⟨39066354075079154014379779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52088472100105538685839705 39066354075079154014379779)
      ·
        refine ⟨58599531112618731021569669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39066354075079154014379779 58599531112618731021569669)
        ·
          refine ⟨10987412083616012066544313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58599531112618731021569669 10987412083616012066544313)
          ·
            refine ⟨8240559062712009049908235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10987412083616012066544313 8240559062712009049908235)
            ·
              refine ⟨12360838594068013574862353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240559062712009049908235 12360838594068013574862353)
              ·
                refine ⟨9270628945551010181146765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12360838594068013574862353 9270628945551010181146765)
                ·
                  refine ⟨3476485854581628817930037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9270628945551010181146765 3476485854581628817930037)
                  ·
                    refine ⟨325920548867027701680941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3476485854581628817930037 325920548867027701680941)
                    ·
                      rfl

theorem cell23_1904184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_1904184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904184 prefixEnd_1904184 := by exact prefixLift 1904184
  have htrace : WordTrace (prefixWord ++ tailWord_1904184) baseStart_1904184 baseEnd_1904184 := by
    simpa [prefixWord, tailWord_1904184, baseEnd_1904184] using wordTrace_append hprefix tailTrace_1904184
  have hstable : (prefixWord ++ tailWord_1904184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904184).length < 2 ^ (prefixWord ++ tailWord_1904184).sum := by decide
  have hdescent : baseEnd_1904184 < baseStart_1904184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904215 : List Nat := [1, 1, 3, 2, 2, 4, 2, 3, 1, 1, 3]
def baseStart_1904215 : Nat := 118140960795 + 1904215 * 2 ^ 59
def prefixEnd_1904215 : Nat := 4983230072969 + 3 ^ 40 * 1904215 * 2
def baseEnd_1904215 : Nat := 977777564501372483755181

theorem tailTrace_1904215 : CollatzResearch.WordTrace tailWord_1904215 prefixEnd_1904215 977777564501372483755181 := by
  unfold tailWord_1904215
  simp only [CollatzResearch.WordTrace]
  refine ⟨69452426796361743875498099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46301617864241162583665399 69452426796361743875498099)
  ·
    refine ⟨104178640194542615813247149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69452426796361743875498099 104178640194542615813247149)
    ·
      refine ⟨39066990072953480929967681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104178640194542615813247149 39066990072953480929967681)
      ·
        refine ⟨29300242554715110697475761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39066990072953480929967681 29300242554715110697475761)
        ·
          refine ⟨21975181916036333023106821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29300242554715110697475761 21975181916036333023106821)
          ·
            refine ⟨4120346609256812441832529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21975181916036333023106821 4120346609256812441832529)
            ·
              refine ⟨3090259956942609331374397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4120346609256812441832529 3090259956942609331374397)
              ·
                refine ⟨1158847483853478499265399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3090259956942609331374397 1158847483853478499265399)
                ·
                  refine ⟨1738271225780217748898099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158847483853478499265399 1738271225780217748898099)
                  ·
                    refine ⟨2607406838670326623347149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1738271225780217748898099 2607406838670326623347149)
                    ·
                      refine ⟨977777564501372483755181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607406838670326623347149 977777564501372483755181)
                      ·
                        rfl

theorem cell23_1904215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_1904215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904215 prefixEnd_1904215 := by exact prefixLift 1904215
  have htrace : WordTrace (prefixWord ++ tailWord_1904215) baseStart_1904215 baseEnd_1904215 := by
    simpa [prefixWord, tailWord_1904215, baseEnd_1904215] using wordTrace_append hprefix tailTrace_1904215
  have hstable : (prefixWord ++ tailWord_1904215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904215).length < 2 ^ (prefixWord ++ tailWord_1904215).sum := by decide
  have hdescent : baseEnd_1904215 < baseStart_1904215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904224 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1904224 : Nat := 118140960795 + 1904224 * 2 ^ 59
def prefixEnd_1904224 : Nat := 4983230072969 + 3 ^ 40 * 1904224 * 2
def baseEnd_1904224 : Nat := 977782185827262948542639

theorem tailTrace_1904224 : CollatzResearch.WordTrace tailWord_1904224 prefixEnd_1904224 977782185827262948542639 := by
  unfold tailWord_1904224
  simp only [CollatzResearch.WordTrace]
  refine ⟨34726377526664569206287863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46301836702219425608383817 34726377526664569206287863)
  ·
    refine ⟨52089566289996853809431795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34726377526664569206287863 52089566289996853809431795)
    ·
      refine ⟨78134349434995280714147693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52089566289996853809431795 78134349434995280714147693)
      ·
        refine ⟨29300381038123230267805385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78134349434995280714147693 29300381038123230267805385)
        ·
          refine ⟨21975285778592422700854039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29300381038123230267805385 21975285778592422700854039)
          ·
            refine ⟨32962928667888634051281059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21975285778592422700854039 32962928667888634051281059)
            ·
              refine ⟨49444393001832951076921589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32962928667888634051281059 49444393001832951076921589)
              ·
                refine ⟨4635411843921839163461399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49444393001832951076921589 4635411843921839163461399)
                ·
                  refine ⟨6953117765882758745192099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635411843921839163461399 6953117765882758745192099)
                  ·
                    refine ⟨10429676648824138117788149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6953117765882758745192099 10429676648824138117788149)
                    ·
                      refine ⟨977782185827262948542639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10429676648824138117788149 977782185827262948542639)
                      ·
                        rfl

theorem cell23_1904224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1904224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904224 prefixEnd_1904224 := by exact prefixLift 1904224
  have htrace : WordTrace (prefixWord ++ tailWord_1904224) baseStart_1904224 baseEnd_1904224 := by
    simpa [prefixWord, tailWord_1904224, baseEnd_1904224] using wordTrace_append hprefix tailTrace_1904224
  have hstable : (prefixWord ++ tailWord_1904224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904224).length < 2 ^ (prefixWord ++ tailWord_1904224).sum := by decide
  have hdescent : baseEnd_1904224 < baseStart_1904224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904288 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1904288 : Nat := 118140960795 + 1904288 * 2 ^ 59
def prefixEnd_1904288 : Nat := 4983230072969 + 3 ^ 40 * 1904288 * 2
def baseEnd_1904288 : Nat := 977815048589150698142345

theorem tailTrace_1904288 : CollatzResearch.WordTrace tailWord_1904288 prefixEnd_1904288 977815048589150698142345 := by
  unfold tailWord_1904288
  simp only [CollatzResearch.WordTrace]
  refine ⟨34727544662548638671452759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46303392883398184895270345 34727544662548638671452759)
  ·
    refine ⟨52091316993822958007179139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34727544662548638671452759 52091316993822958007179139)
    ·
      refine ⟨78136975490734437010768709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52091316993822958007179139 78136975490734437010768709)
      ·
        refine ⟨14650682904512706939519133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78136975490734437010768709 14650682904512706939519133)
        ·
          refine ⟨5494006089192265102319675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14650682904512706939519133 5494006089192265102319675)
          ·
            refine ⟨8241009133788397653479513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494006089192265102319675 8241009133788397653479513)
            ·
              refine ⟨6180756850341298240109635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8241009133788397653479513 6180756850341298240109635)
              ·
                refine ⟨9271135275511947360164453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180756850341298240109635 9271135275511947360164453)
                ·
                  refine ⟨1738337864158490130030835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9271135275511947360164453 1738337864158490130030835)
                  ·
                    refine ⟨2607506796237735195046253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1738337864158490130030835 2607506796237735195046253)
                    ·
                      refine ⟨977815048589150698142345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607506796237735195046253 977815048589150698142345)
                      ·
                        rfl

theorem cell23_1904288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1904288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904288 prefixEnd_1904288 := by exact prefixLift 1904288
  have htrace : WordTrace (prefixWord ++ tailWord_1904288) baseStart_1904288 baseEnd_1904288 := by
    simpa [prefixWord, tailWord_1904288, baseEnd_1904288] using wordTrace_append hprefix tailTrace_1904288
  have hstable : (prefixWord ++ tailWord_1904288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904288).length < 2 ^ (prefixWord ++ tailWord_1904288).sum := by decide
  have hdescent : baseEnd_1904288 < baseStart_1904288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904289 : List Nat := [1, 2, 3, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1904289 : Nat := 118140960795 + 1904289 * 2 ^ 59
def prefixEnd_1904289 : Nat := 4983230072969 + 3 ^ 40 * 1904289 * 2
def baseEnd_1904289 : Nat := 977815562069805194229841

theorem tailTrace_1904289 : CollatzResearch.WordTrace tailWord_1904289 prefixEnd_1904289 977815562069805194229841 := by
  unfold tailWord_1904289
  simp only [CollatzResearch.WordTrace]
  refine ⟨69455125798093654513691921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46303417198729103009127947 69455125798093654513691921)
  ·
    refine ⟨52091344348570240885268941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69455125798093654513691921 52091344348570240885268941)
    ·
      refine ⟨19534254130713840331975853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52091344348570240885268941 19534254130713840331975853)
      ·
        refine ⟨7325345299017690124490945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19534254130713840331975853 7325345299017690124490945)
        ·
          refine ⟨5494008974263267593368209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7325345299017690124490945 5494008974263267593368209)
          ·
            refine ⟨4120506730697450695026157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5494008974263267593368209 4120506730697450695026157)
            ·
              refine ⟨1545190024011544010634809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4120506730697450695026157 1545190024011544010634809)
              ·
                refine ⟨1158892518008658007976107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545190024011544010634809 1158892518008658007976107)
                ·
                  refine ⟨1738338777012987011964161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158892518008658007976107 1738338777012987011964161)
                  ·
                    refine ⟨1303754082759740258973121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738338777012987011964161 1303754082759740258973121)
                    ·
                      refine ⟨977815562069805194229841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303754082759740258973121 977815562069805194229841)
                      ·
                        rfl

theorem cell23_1904289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1904289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904289 prefixEnd_1904289 := by exact prefixLift 1904289
  have htrace : WordTrace (prefixWord ++ tailWord_1904289) baseStart_1904289 baseEnd_1904289 := by
    simpa [prefixWord, tailWord_1904289, baseEnd_1904289] using wordTrace_append hprefix tailTrace_1904289
  have hstable : (prefixWord ++ tailWord_1904289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904289).length < 2 ^ (prefixWord ++ tailWord_1904289).sum := by decide
  have hdescent : baseEnd_1904289 < baseStart_1904289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904304 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 2, 6]
def baseStart_1904304 : Nat := 118140960795 + 1904304 * 2 ^ 59
def prefixEnd_1904304 : Nat := 4983230072969 + 3 ^ 40 * 1904304 * 2
def baseEnd_1904304 : Nat := 325941088093207545180757

theorem tailTrace_1904304 : CollatzResearch.WordTrace tailWord_1904304 prefixEnd_1904304 325941088093207545180757 := by
  unfold tailWord_1904304
  simp only [CollatzResearch.WordTrace]
  refine ⟨34727836446519656037743983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46303781928692874716991977 34727836446519656037743983)
  ·
    refine ⟨52091754669779484056615975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34727836446519656037743983 52091754669779484056615975)
    ·
      refine ⟨78137632004669226084923963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52091754669779484056615975 78137632004669226084923963)
      ·
        refine ⟨117206448007003839127385945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78137632004669226084923963 117206448007003839127385945)
        ·
          refine ⟨87904836005252879345539459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117206448007003839127385945 87904836005252879345539459)
          ·
            refine ⟨131857254007879319018309189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87904836005252879345539459 131857254007879319018309189)
            ·
              refine ⟨24723235126477372315932973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131857254007879319018309189 24723235126477372315932973)
              ·
                refine ⟨9271213172429014618474865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24723235126477372315932973 9271213172429014618474865)
                ·
                  refine ⟨6953409879321760963856149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9271213172429014618474865 6953409879321760963856149)
                  ·
                    refine ⟨325941088093207545180757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6953409879321760963856149 325941088093207545180757)
                    ·
                      rfl

theorem cell23_1904304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_1904304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904304 prefixEnd_1904304 := by exact prefixLift 1904304
  have htrace : WordTrace (prefixWord ++ tailWord_1904304) baseStart_1904304 baseEnd_1904304 := by
    simpa [prefixWord, tailWord_1904304, baseEnd_1904304] using wordTrace_append hprefix tailTrace_1904304
  have hstable : (prefixWord ++ tailWord_1904304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904304).length < 2 ^ (prefixWord ++ tailWord_1904304).sum := by decide
  have hdescent : baseEnd_1904304 < baseStart_1904304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904328 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_1904328 : Nat := 118140960795 + 1904328 * 2 ^ 59
def prefixEnd_1904328 : Nat := 4983230072969 + 3 ^ 40 * 1904328 * 2
def baseEnd_1904328 : Nat := 977835587815330541642161

theorem tailTrace_1904328 : CollatzResearch.WordTrace tailWord_1904328 prefixEnd_1904328 977835587815330541642161 := by
  unfold tailWord_1904328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34728274122476182087180819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46304365496634909449574425 34728274122476182087180819)
  ·
    refine ⟨52092411183714273130771229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34728274122476182087180819 52092411183714273130771229)
    ·
      refine ⟨19534654193892852424039211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52092411183714273130771229 19534654193892852424039211)
      ·
        refine ⟨29301981290839278636058817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19534654193892852424039211 29301981290839278636058817)
        ·
          refine ⟨21976485968129458977044113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29301981290839278636058817 21976485968129458977044113)
          ·
            refine ⟨16482364476097094232783085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21976485968129458977044113 16482364476097094232783085)
            ·
              refine ⟨6180886678536410337293657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16482364476097094232783085 6180886678536410337293657)
              ·
                refine ⟨4635665008902307752970243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6180886678536410337293657 4635665008902307752970243)
                ·
                  refine ⟨6953497513353461629455365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635665008902307752970243 6953497513353461629455365)
                  ·
                    refine ⟨1303780783753774055522881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6953497513353461629455365 1303780783753774055522881)
                    ·
                      refine ⟨977835587815330541642161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303780783753774055522881 977835587815330541642161)
                      ·
                        rfl

theorem cell23_1904328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_1904328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904328 prefixEnd_1904328 := by exact prefixLift 1904328
  have htrace : WordTrace (prefixWord ++ tailWord_1904328) baseStart_1904328 baseEnd_1904328 := by
    simpa [prefixWord, tailWord_1904328, baseEnd_1904328] using wordTrace_append hprefix tailTrace_1904328
  have hstable : (prefixWord ++ tailWord_1904328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904328).length < 2 ^ (prefixWord ++ tailWord_1904328).sum := by decide
  have hdescent : baseEnd_1904328 < baseStart_1904328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904345 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 2, 2, 2]
def baseStart_1904345 : Nat := 118140960795 + 1904345 * 2 ^ 59
def prefixEnd_1904345 : Nat := 4983230072969 + 3 ^ 40 * 1904345 * 2
def baseEnd_1904345 : Nat := 977844316986456975129583

theorem tailTrace_1904345 : CollatzResearch.WordTrace tailWord_1904345 prefixEnd_1904345 977844316986456975129583 := by
  unfold tailWord_1904345
  simp only [CollatzResearch.WordTrace]
  refine ⟨69457168285890776077730489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46304778857260517385153659 69457168285890776077730489)
  ·
    refine ⟨52092876214418082058297867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69457168285890776077730489 52092876214418082058297867)
    ·
      refine ⟨78139314321627123087446801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52092876214418082058297867 78139314321627123087446801)
      ·
        refine ⟨58604485741220342315585101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78139314321627123087446801 58604485741220342315585101)
        ·
          refine ⟨21976682152957628368344413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58604485741220342315585101 21976682152957628368344413)
          ·
            refine ⟨8241255807359110638129155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21976682152957628368344413 8241255807359110638129155)
            ·
              refine ⟨12361883711038665957193733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241255807359110638129155 12361883711038665957193733)
              ·
                refine ⟨2317853195819749866973825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12361883711038665957193733 2317853195819749866973825)
                ·
                  refine ⟨1738389896864812400230369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2317853195819749866973825 1738389896864812400230369)
                  ·
                    refine ⟨1303792422648609300172777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738389896864812400230369 1303792422648609300172777)
                    ·
                      refine ⟨977844316986456975129583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303792422648609300172777 977844316986456975129583)
                      ·
                        rfl

theorem cell23_1904345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_1904345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904345 prefixEnd_1904345 := by exact prefixLift 1904345
  have htrace : WordTrace (prefixWord ++ tailWord_1904345) baseStart_1904345 baseEnd_1904345 := by
    simpa [prefixWord, tailWord_1904345, baseEnd_1904345] using wordTrace_append hprefix tailTrace_1904345
  have hstable : (prefixWord ++ tailWord_1904345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904345).length < 2 ^ (prefixWord ++ tailWord_1904345).sum := by decide
  have hdescent : baseEnd_1904345 < baseStart_1904345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904381 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_1904381 : Nat := 118140960795 + 1904381 * 2 ^ 59
def prefixEnd_1904381 : Nat := 4983230072969 + 3 ^ 40 * 1904381 * 2
def baseEnd_1904381 : Nat := 325954267430006278093139

theorem tailTrace_1904381 : CollatzResearch.WordTrace tailWord_1904381 prefixEnd_1904381 325954267430006278093139 := by
  unfold tailWord_1904381
  simp only [CollatzResearch.WordTrace]
  refine ⟨69458481313760354226040997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46305654209173569484027331 69458481313760354226040997)
  ·
    refine ⟨13023465246330066417382687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69458481313760354226040997 13023465246330066417382687)
    ·
      refine ⟨19535197869495099626074031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13023465246330066417382687 19535197869495099626074031)
      ·
        refine ⟨29302796804242649439111047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535197869495099626074031 29302796804242649439111047)
        ·
          refine ⟨43954195206363974158666571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29302796804242649439111047 43954195206363974158666571)
          ·
            refine ⟨65931292809545961237999857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43954195206363974158666571 65931292809545961237999857)
            ·
              refine ⟨49448469607159470928499893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65931292809545961237999857 49448469607159470928499893)
              ·
                refine ⟨4635794025671200399546865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49448469607159470928499893 4635794025671200399546865)
                ·
                  refine ⟨3476845519253400299660149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635794025671200399546865 3476845519253400299660149)
                  ·
                    refine ⟨325954267430006278093139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3476845519253400299660149 325954267430006278093139)
                    ·
                      rfl

theorem cell23_1904381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_1904381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904381 prefixEnd_1904381 := by exact prefixLift 1904381
  have htrace : WordTrace (prefixWord ++ tailWord_1904381) baseStart_1904381 baseEnd_1904381 := by
    simpa [prefixWord, tailWord_1904381, baseEnd_1904381] using wordTrace_append hprefix tailTrace_1904381
  have hstable : (prefixWord ++ tailWord_1904381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904381).length < 2 ^ (prefixWord ++ tailWord_1904381).sum := by decide
  have hdescent : baseEnd_1904381 < baseStart_1904381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904390 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1904390 : Nat := 118140960795 + 1904390 * 2 ^ 59
def prefixEnd_1904390 : Nat := 4983230072969 + 3 ^ 40 * 1904390 * 2
def baseEnd_1904390 : Nat := 977867423615909299066877

theorem tailTrace_1904390 : CollatzResearch.WordTrace tailWord_1904390 prefixEnd_1904390 977867423615909299066877 := by
  unfold tailWord_1904390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170587799085242148847457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46305873047151832508745749 2170587799085242148847457)
  ·
    refine ⟨1627940849313931611635593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2170587799085242148847457 1627940849313931611635593)
    ·
      refine ⟨1220955636985448708726695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1627940849313931611635593 1220955636985448708726695)
      ·
        refine ⟨1831433455478173063090043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220955636985448708726695 1831433455478173063090043)
        ·
          refine ⟨2747150183217259594635065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831433455478173063090043 2747150183217259594635065)
          ·
            refine ⟨2060362637412944695976299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2747150183217259594635065 2060362637412944695976299)
            ·
              refine ⟨3090543956119417043964449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060362637412944695976299 3090543956119417043964449)
              ·
                refine ⟨2317907967089562782973337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3090543956119417043964449 2317907967089562782973337)
                ·
                  refine ⟨1738430975317172087230003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2317907967089562782973337 1738430975317172087230003)
                  ·
                    refine ⟨2607646462975758130845005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1738430975317172087230003 2607646462975758130845005)
                    ·
                      refine ⟨977867423615909299066877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607646462975758130845005 977867423615909299066877)
                      ·
                        rfl

theorem cell23_1904390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1904390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904390 prefixEnd_1904390 := by exact prefixLift 1904390
  have htrace : WordTrace (prefixWord ++ tailWord_1904390) baseStart_1904390 baseEnd_1904390 := by
    simpa [prefixWord, tailWord_1904390, baseEnd_1904390] using wordTrace_append hprefix tailTrace_1904390
  have hstable : (prefixWord ++ tailWord_1904390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904390).length < 2 ^ (prefixWord ++ tailWord_1904390).sum := by decide
  have hdescent : baseEnd_1904390 < baseStart_1904390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904401 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_1904401 : Nat := 118140960795 + 1904401 * 2 ^ 59
def prefixEnd_1904401 : Nat := 4983230072969 + 3 ^ 40 * 1904401 * 2
def baseEnd_1904401 : Nat := 977873071903108756029325

theorem tailTrace_1904401 : CollatzResearch.WordTrace tailWord_1904401 prefixEnd_1904401 977873071903108756029325 := by
  unfold tailWord_1904401
  simp only [CollatzResearch.WordTrace]
  refine ⟨69459210773687897641769057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46306140515791931761179371 69459210773687897641769057)
  ·
    refine ⟨52094408080265923231326793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69459210773687897641769057 52094408080265923231326793)
    ·
      refine ⟨39070806060199442423495095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52094408080265923231326793 39070806060199442423495095)
      ·
        refine ⟨58606209090299163635242643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39070806060199442423495095 58606209090299163635242643)
        ·
          refine ⟨87909313635448745452863965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58606209090299163635242643 87909313635448745452863965)
          ·
            refine ⟨32965992613293279544823987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87909313635448745452863965 32965992613293279544823987)
            ·
              refine ⟨49448988919939919317235981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32965992613293279544823987 49448988919939919317235981)
              ·
                refine ⟨18543370844977469743963493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49448988919939919317235981 18543370844977469743963493)
                ·
                  refine ⟨3476882033433275576993155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18543370844977469743963493 3476882033433275576993155)
                  ·
                    refine ⟨5215323050149913365489733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3476882033433275576993155 5215323050149913365489733)
                    ·
                      refine ⟨977873071903108756029325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5215323050149913365489733 977873071903108756029325)
                      ·
                        rfl

theorem cell23_1904401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_1904401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904401 prefixEnd_1904401 := by exact prefixLift 1904401
  have htrace : WordTrace (prefixWord ++ tailWord_1904401) baseStart_1904401 baseEnd_1904401 := by
    simpa [prefixWord, tailWord_1904401, baseEnd_1904401] using wordTrace_append hprefix tailTrace_1904401
  have hstable : (prefixWord ++ tailWord_1904401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904401).length < 2 ^ (prefixWord ++ tailWord_1904401).sum := by decide
  have hdescent : baseEnd_1904401 < baseStart_1904401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904411 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 7, 4]
def baseStart_1904411 : Nat := 118140960795 + 1904411 * 2 ^ 59
def prefixEnd_1904411 : Nat := 4983230072969 + 3 ^ 40 * 1904411 * 2
def baseEnd_1904411 : Nat := 325959402236551238968093

theorem tailTrace_1904411 : CollatzResearch.WordTrace tailWord_1904411 prefixEnd_1904411 325959402236551238968093 := by
  unfold tailWord_1904411
  simp only [CollatzResearch.WordTrace]
  refine ⟨69459575503651669349633087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46306383669101112899755391 69459575503651669349633087)
  ·
    refine ⟨104189363255477504024449631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69459575503651669349633087 104189363255477504024449631)
    ·
      refine ⟨156284044883216256036674447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104189363255477504024449631 156284044883216256036674447)
      ·
        refine ⟨234426067324824384055011671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156284044883216256036674447 234426067324824384055011671)
        ·
          refine ⟨351639100987236576082517507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234426067324824384055011671 351639100987236576082517507)
          ·
            refine ⟨527458651480854864123776261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351639100987236576082517507 527458651480854864123776261)
            ·
              refine ⟨98898497152660287023208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 527458651480854864123776261 98898497152660287023208049)
              ·
                refine ⟨74173872864495215267406037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98898497152660287023208049 74173872864495215267406037)
                ·
                  refine ⟨1738450145261606607829829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74173872864495215267406037 1738450145261606607829829)
                  ·
                    refine ⟨325959402236551238968093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1738450145261606607829829 325959402236551238968093)
                    ·
                      rfl

theorem cell23_1904411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 4].length) (baseStart_1904411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904411 prefixEnd_1904411 := by exact prefixLift 1904411
  have htrace : WordTrace (prefixWord ++ tailWord_1904411) baseStart_1904411 baseEnd_1904411 := by
    simpa [prefixWord, tailWord_1904411, baseEnd_1904411] using wordTrace_append hprefix tailTrace_1904411
  have hstable : (prefixWord ++ tailWord_1904411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904411).length < 2 ^ (prefixWord ++ tailWord_1904411).sum := by decide
  have hdescent : baseEnd_1904411 < baseStart_1904411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904428 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_1904428 : Nat := 118140960795 + 1904428 * 2 ^ 59
def prefixEnd_1904428 : Nat := 4983230072969 + 3 ^ 40 * 1904428 * 2
def baseEnd_1904428 : Nat := 325962311960260050130567

theorem tailTrace_1904428 : CollatzResearch.WordTrace tailWord_1904428 prefixEnd_1904428 325962311960260050130567 := by
  unfold tailWord_1904428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34730097772295040626500969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46306797029726720835334625 34730097772295040626500969)
  ·
    refine ⟨26047573329221280469875727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34730097772295040626500969 26047573329221280469875727)
    ·
      refine ⟨39071359993831920704813591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26047573329221280469875727 39071359993831920704813591)
      ·
        refine ⟨58607039990747881057220387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39071359993831920704813591 58607039990747881057220387)
        ·
          refine ⟨87910559986121821585830581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58607039990747881057220387 87910559986121821585830581)
          ·
            refine ⟨8241614998698920773671617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87910559986121821585830581 8241614998698920773671617)
            ·
              refine ⟨6181211249024190580253713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8241614998698920773671617 6181211249024190580253713)
              ·
                refine ⟨4635908436768142935190285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181211249024190580253713 4635908436768142935190285)
                ·
                  refine ⟨1738465663788053600696357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4635908436768142935190285 1738465663788053600696357)
                  ·
                    refine ⟨325962311960260050130567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1738465663788053600696357 325962311960260050130567)
                    ·
                      rfl

theorem cell23_1904428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_1904428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904428 prefixEnd_1904428 := by exact prefixLift 1904428
  have htrace : WordTrace (prefixWord ++ tailWord_1904428) baseStart_1904428 baseEnd_1904428 := by
    simpa [prefixWord, tailWord_1904428, baseEnd_1904428] using wordTrace_append hprefix tailTrace_1904428
  have hstable : (prefixWord ++ tailWord_1904428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904428).length < 2 ^ (prefixWord ++ tailWord_1904428).sum := by decide
  have hdescent : baseEnd_1904428 < baseStart_1904428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904488 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1904488 : Nat := 118140960795 + 1904488 * 2 ^ 59
def prefixEnd_1904488 : Nat := 4983230072969 + 3 ^ 40 * 1904488 * 2
def baseEnd_1904488 : Nat := 325972581573349971880475

theorem tailTrace_1904488 : CollatzResearch.WordTrace tailWord_1904488 prefixEnd_1904488 325972581573349971880475 := by
  unfold tailWord_1904488
  simp only [CollatzResearch.WordTrace]
  refine ⟨34731191962186355750093059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46308255949581807666790745 34731191962186355750093059)
  ·
    refine ⟨52096787943279533625139589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34731191962186355750093059 52096787943279533625139589)
    ·
      refine ⟨9768147739364912554713673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52096787943279533625139589 9768147739364912554713673)
      ·
        refine ⟨7326110804523684416035255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9768147739364912554713673 7326110804523684416035255)
        ·
          refine ⟨10989166206785526624052883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326110804523684416035255 10989166206785526624052883)
          ·
            refine ⟨16483749310178289936079325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10989166206785526624052883 16483749310178289936079325)
            ·
              refine ⟨6181405991316858726029747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16483749310178289936079325 6181405991316858726029747)
              ·
                refine ⟨9272108986975288089044621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181405991316858726029747 9272108986975288089044621)
                ·
                  refine ⟨3477040870115733033391733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9272108986975288089044621 3477040870115733033391733)
                  ·
                    refine ⟨325972581573349971880475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3477040870115733033391733 325972581573349971880475)
                    ·
                      rfl

theorem cell23_1904488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1904488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904488 prefixEnd_1904488 := by exact prefixLift 1904488
  have htrace : WordTrace (prefixWord ++ tailWord_1904488) baseStart_1904488 baseEnd_1904488 := by
    simpa [prefixWord, tailWord_1904488, baseEnd_1904488] using wordTrace_append hprefix tailTrace_1904488
  have hstable : (prefixWord ++ tailWord_1904488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904488).length < 2 ^ (prefixWord ++ tailWord_1904488).sum := by decide
  have hdescent : baseEnd_1904488 < baseStart_1904488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904505 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 1, 5]
def baseStart_1904505 : Nat := 118140960795 + 1904505 * 2 ^ 59
def prefixEnd_1904505 : Nat := 4983230072969 + 3 ^ 40 * 1904505 * 2
def baseEnd_1904505 : Nat := 325975491297058783042949

theorem tailTrace_1904505 : CollatzResearch.WordTrace tailWord_1904505 prefixEnd_1904505 325975491297058783042949 := by
  unfold tailWord_1904505
  simp only [CollatzResearch.WordTrace]
  refine ⟨69463003965311123403554969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46308669310207415602369979 69463003965311123403554969)
  ·
    refine ⟨52097252973983342552666227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69463003965311123403554969 52097252973983342552666227)
    ·
      refine ⟨78145879460975013828999341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52097252973983342552666227 78145879460975013828999341)
      ·
        refine ⟨29304704797865630185874753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78145879460975013828999341 29304704797865630185874753)
        ·
          refine ⟨21978528598399222639406065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29304704797865630185874753 21978528598399222639406065)
          ·
            refine ⟨16483896448799416979554549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21978528598399222639406065 16483896448799416979554549)
            ·
              refine ⟨1545365292074945341833239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16483896448799416979554549 1545365292074945341833239)
              ·
                refine ⟨2318047938112418012749859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545365292074945341833239 2318047938112418012749859)
                ·
                  refine ⟨3477071907168627019124789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318047938112418012749859 3477071907168627019124789)
                  ·
                    refine ⟨325975491297058783042949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3477071907168627019124789 325975491297058783042949)
                    ·
                      rfl

theorem cell23_1904505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 5].length) (baseStart_1904505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904505 prefixEnd_1904505 := by exact prefixLift 1904505
  have htrace : WordTrace (prefixWord ++ tailWord_1904505) baseStart_1904505 baseEnd_1904505 := by
    simpa [prefixWord, tailWord_1904505, baseEnd_1904505] using wordTrace_append hprefix tailTrace_1904505
  have hstable : (prefixWord ++ tailWord_1904505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904505).length < 2 ^ (prefixWord ++ tailWord_1904505).sum := by decide
  have hdescent : baseEnd_1904505 < baseStart_1904505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904513 : List Nat := [1, 2, 4, 4, 2, 1, 2, 2, 1, 4]
def baseStart_1904513 : Nat := 118140960795 + 1904513 * 2 ^ 59
def prefixEnd_1904513 : Nat := 4983230072969 + 3 ^ 40 * 1904513 * 2
def baseEnd_1904513 : Nat := 325976860578804105942937

theorem tailTrace_1904513 : CollatzResearch.WordTrace tailWord_1904513 prefixEnd_1904513 325976860578804105942937 := by
  unfold tailWord_1904513
  simp only [CollatzResearch.WordTrace]
  refine ⟨69463295749282140769846193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46308863832854760513230795 69463295749282140769846193)
  ·
    refine ⟨52097471811961605577384645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69463295749282140769846193 52097471811961605577384645)
    ·
      refine ⟨9768275964742801045759621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52097471811961605577384645 9768275964742801045759621)
      ·
        refine ⟨1831551743389275196079929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9768275964742801045759621 1831551743389275196079929)
        ·
          refine ⟨1373663807541956397059947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831551743389275196079929 1373663807541956397059947)
          ·
            refine ⟨2060495711312934595589921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373663807541956397059947 2060495711312934595589921)
            ·
              refine ⟨1545371783484700946692441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060495711312934595589921 1545371783484700946692441)
              ·
                refine ⟨1159028837613525710019331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545371783484700946692441 1159028837613525710019331)
                ·
                  refine ⟨1738543256420288565028997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159028837613525710019331 1738543256420288565028997)
                  ·
                    refine ⟨325976860578804105942937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1738543256420288565028997 325976860578804105942937)
                    ·
                      rfl

theorem cell23_1904513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_1904513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904513 prefixEnd_1904513 := by exact prefixLift 1904513
  have htrace : WordTrace (prefixWord ++ tailWord_1904513) baseStart_1904513 baseEnd_1904513 := by
    simpa [prefixWord, tailWord_1904513, baseEnd_1904513] using wordTrace_append hprefix tailTrace_1904513
  have hstable : (prefixWord ++ tailWord_1904513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904513).length < 2 ^ (prefixWord ++ tailWord_1904513).sum := by decide
  have hdescent : baseEnd_1904513 < baseStart_1904513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904519 : List Nat := [1, 1, 4, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_1904519 : Nat := 118140960795 + 1904519 * 2 ^ 59
def prefixEnd_1904519 : Nat := 4983230072969 + 3 ^ 40 * 1904519 * 2
def baseEnd_1904519 : Nat := 977933662620339294353783

theorem tailTrace_1904519 : CollatzResearch.WordTrace tailWord_1904519 prefixEnd_1904519 977933662620339294353783 := by
  unfold tailWord_1904519
  simp only [CollatzResearch.WordTrace]
  refine ⟨69463514587260403794564611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46309009724840269196376407 69463514587260403794564611)
  ·
    refine ⟨104195271880890605691846917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69463514587260403794564611 104195271880890605691846917)
    ·
      refine ⟨19536613477666988567221297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104195271880890605691846917 19536613477666988567221297)
      ·
        refine ⟨14652460108250241425415973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19536613477666988567221297 14652460108250241425415973)
        ·
          refine ⟨2747336270296920267265495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14652460108250241425415973 2747336270296920267265495)
          ·
            refine ⟨4121004405445380400898243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747336270296920267265495 4121004405445380400898243)
            ·
              refine ⟨6181506608168070601347365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121004405445380400898243 6181506608168070601347365)
              ·
                refine ⟨1159032489031513237752631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6181506608168070601347365 1159032489031513237752631)
                ·
                  refine ⟨1738548733547269856628947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159032489031513237752631 1738548733547269856628947)
                  ·
                    refine ⟨2607823100320904784943421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1738548733547269856628947 2607823100320904784943421)
                    ·
                      refine ⟨977933662620339294353783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607823100320904784943421 977933662620339294353783)
                      ·
                        rfl

theorem cell23_1904519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_1904519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904519 prefixEnd_1904519 := by exact prefixLift 1904519
  have htrace : WordTrace (prefixWord ++ tailWord_1904519) baseStart_1904519 baseEnd_1904519 := by
    simpa [prefixWord, tailWord_1904519, baseEnd_1904519] using wordTrace_append hprefix tailTrace_1904519
  have hstable : (prefixWord ++ tailWord_1904519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904519).length < 2 ^ (prefixWord ++ tailWord_1904519).sum := by decide
  have hdescent : baseEnd_1904519 < baseStart_1904519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904528 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3]
def baseStart_1904528 : Nat := 118140960795 + 1904528 * 2 ^ 59
def prefixEnd_1904528 : Nat := 4983230072969 + 3 ^ 40 * 1904528 * 2
def baseEnd_1904528 : Nat := 977938283946229759141241

theorem tailTrace_1904528 : CollatzResearch.WordTrace tailWord_1904528 prefixEnd_1904528 977938283946229759141241 := by
  unfold tailWord_1904528
  simp only [CollatzResearch.WordTrace]
  refine ⟨34731921422113899165821119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46309228562818532221094825 34731921422113899165821119)
  ·
    refine ⟨52097882133170848748731679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34731921422113899165821119 52097882133170848748731679)
    ·
      refine ⟨78146823199756273123097519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52097882133170848748731679 78146823199756273123097519)
      ·
        refine ⟨117220234799634409684646279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78146823199756273123097519 117220234799634409684646279)
        ·
          refine ⟨175830352199451614526969419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117220234799634409684646279 175830352199451614526969419)
          ·
            refine ⟨263745528299177421790454129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175830352199451614526969419 263745528299177421790454129)
            ·
              refine ⟨197809146224383066342840597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263745528299177421790454129 197809146224383066342840597)
              ·
                refine ⟨9272303729267956234820653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197809146224383066342840597 9272303729267956234820653)
                ·
                  refine ⟨3477113898475483588057745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9272303729267956234820653 3477113898475483588057745)
                  ·
                    refine ⟨2607835423856612691043309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3477113898475483588057745 2607835423856612691043309)
                    ·
                      refine ⟨977938283946229759141241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607835423856612691043309 977938283946229759141241)
                      ·
                        rfl

theorem cell23_1904528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_1904528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904528 prefixEnd_1904528 := by exact prefixLift 1904528
  have htrace : WordTrace (prefixWord ++ tailWord_1904528) baseStart_1904528 baseEnd_1904528 := by
    simpa [prefixWord, tailWord_1904528, baseEnd_1904528] using wordTrace_append hprefix tailTrace_1904528
  have hstable : (prefixWord ++ tailWord_1904528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904528).length < 2 ^ (prefixWord ++ tailWord_1904528).sum := by decide
  have hdescent : baseEnd_1904528 < baseStart_1904528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904535 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 2, 4]
def baseStart_1904535 : Nat := 118140960795 + 1904535 * 2 ^ 59
def prefixEnd_1904535 : Nat := 4983230072969 + 3 ^ 40 * 1904535 * 2
def baseEnd_1904535 : Nat := 325980626103603743917903

theorem tailTrace_1904535 : CollatzResearch.WordTrace tailWord_1904535 prefixEnd_1904535 325980626103603743917903 := by
  unfold tailWord_1904535
  simp only [CollatzResearch.WordTrace]
  refine ⟨69464098155202438527147059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46309398770134959018098039 69464098155202438527147059)
  ·
    refine ⟨104196147232803657790720589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69464098155202438527147059 104196147232803657790720589)
    ·
      refine ⟨39073555212301371671520221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104196147232803657790720589 39073555212301371671520221)
      ·
        refine ⟨14652583204613014376820083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39073555212301371671520221 14652583204613014376820083)
        ·
          refine ⟨21978874806919521565230125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14652583204613014376820083 21978874806919521565230125)
          ·
            refine ⟨8242078052594820586961297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21978874806919521565230125 8242078052594820586961297)
            ·
              refine ⟨6181558539446115440220973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8242078052594820586961297 6181558539446115440220973)
              ·
                refine ⟨2318084452292293290082865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6181558539446115440220973 2318084452292293290082865)
                ·
                  refine ⟨1738563339219219967562149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2318084452292293290082865 1738563339219219967562149)
                  ·
                    refine ⟨325980626103603743917903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1738563339219219967562149 325980626103603743917903)
                    ·
                      rfl

theorem cell23_1904535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_1904535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904535 prefixEnd_1904535 := by exact prefixLift 1904535
  have htrace : WordTrace (prefixWord ++ tailWord_1904535) baseStart_1904535 baseEnd_1904535 := by
    simpa [prefixWord, tailWord_1904535, baseEnd_1904535] using wordTrace_append hprefix tailTrace_1904535
  have hstable : (prefixWord ++ tailWord_1904535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904535).length < 2 ^ (prefixWord ++ tailWord_1904535).sum := by decide
  have hdescent : baseEnd_1904535 < baseStart_1904535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904546 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1904546 : Nat := 118140960795 + 1904546 * 2 ^ 59
def prefixEnd_1904546 : Nat := 4983230072969 + 3 ^ 40 * 1904546 * 2
def baseEnd_1904546 : Nat := 977947526598010688716159

theorem tailTrace_1904546 : CollatzResearch.WordTrace tailWord_1904546 prefixEnd_1904546 977947526598010688716159 := by
  unfold tailWord_1904546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17366124839540646851449373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46309666238775058270531661 17366124839540646851449373)
  ·
    refine ⟨6512296814827742569293515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17366124839540646851449373 6512296814827742569293515)
    ·
      refine ⟨9768445222241613853940273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512296814827742569293515 9768445222241613853940273)
      ·
        refine ⟨7326333916681210390455205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9768445222241613853940273 7326333916681210390455205)
        ·
          refine ⟨1373687609377726948210351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7326333916681210390455205 1373687609377726948210351)
          ·
            refine ⟨2060531414066590422315527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373687609377726948210351 2060531414066590422315527)
            ·
              refine ⟨3090797121099885633473291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060531414066590422315527 3090797121099885633473291)
              ·
                refine ⟨4636195681649828450209937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090797121099885633473291 4636195681649828450209937)
                ·
                  refine ⟨3477146761237371337657453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636195681649828450209937 3477146761237371337657453)
                  ·
                    refine ⟨1303930035464014251621545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477146761237371337657453 1303930035464014251621545)
                    ·
                      refine ⟨977947526598010688716159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303930035464014251621545 977947526598010688716159)
                      ·
                        rfl

theorem cell23_1904546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1904546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904546 prefixEnd_1904546 := by exact prefixLift 1904546
  have htrace : WordTrace (prefixWord ++ tailWord_1904546) baseStart_1904546 baseEnd_1904546 := by
    simpa [prefixWord, tailWord_1904546, baseEnd_1904546] using wordTrace_append hprefix tailTrace_1904546
  have hstable : (prefixWord ++ tailWord_1904546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904546).length < 2 ^ (prefixWord ++ tailWord_1904546).sum := by decide
  have hdescent : baseEnd_1904546 < baseStart_1904546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904559 : List Nat := [1, 1, 2, 1, 2, 2, 6, 3, 1, 2, 2]
def baseStart_1904559 : Nat := 118140960795 + 1904559 * 2 ^ 59
def prefixEnd_1904559 : Nat := 4983230072969 + 3 ^ 40 * 1904559 * 2
def baseEnd_1904559 : Nat := 977954201846519137853599

theorem tailTrace_1904559 : CollatzResearch.WordTrace tailWord_1904559 prefixEnd_1904559 977954201846519137853599 := by
  unfold tailWord_1904559
  simp only [CollatzResearch.WordTrace]
  refine ⟨69464973507115490626020731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46309982338076993750680487 69464973507115490626020731)
  ·
    refine ⟨104197460260673235939031097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69464973507115490626020731 104197460260673235939031097)
    ·
      refine ⟨78148095195504926954273323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104197460260673235939031097 78148095195504926954273323)
      ·
        refine ⟨117222142793257390431409985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78148095195504926954273323 117222142793257390431409985)
        ·
          refine ⟨87916607094943042823557489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117222142793257390431409985 87916607094943042823557489)
          ·
            refine ⟨65937455321207282117668117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87916607094943042823557489 65937455321207282117668117)
            ·
              refine ⟨3090818218181591349265693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65937455321207282117668117 3090818218181591349265693)
              ·
                refine ⟨1159056831818096755974635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3090818218181591349265693 1159056831818096755974635)
                ·
                  refine ⟨1738585247727145133961953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159056831818096755974635 1738585247727145133961953)
                  ·
                    refine ⟨1303938935795358850471465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738585247727145133961953 1303938935795358850471465)
                    ·
                      refine ⟨977954201846519137853599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303938935795358850471465 977954201846519137853599)
                      ·
                        rfl

theorem cell23_1904559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 2, 2].length) (baseStart_1904559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904559 prefixEnd_1904559 := by exact prefixLift 1904559
  have htrace : WordTrace (prefixWord ++ tailWord_1904559) baseStart_1904559 baseEnd_1904559 := by
    simpa [prefixWord, tailWord_1904559, baseEnd_1904559] using wordTrace_append hprefix tailTrace_1904559
  have hstable : (prefixWord ++ tailWord_1904559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904559).length < 2 ^ (prefixWord ++ tailWord_1904559).sum := by decide
  have hdescent : baseEnd_1904559 < baseStart_1904559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904575 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 3]
def baseStart_1904575 : Nat := 118140960795 + 1904575 * 2 ^ 59
def prefixEnd_1904575 : Nat := 4983230072969 + 3 ^ 40 * 1904575 * 2
def baseEnd_1904575 : Nat := 977962417536991075253525

theorem tailTrace_1904575 : CollatzResearch.WordTrace tailWord_1904575 prefixEnd_1904575 977962417536991075253525 := by
  unfold tailWord_1904575
  simp only [CollatzResearch.WordTrace]
  refine ⟨69465557075057525358603179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46310371383371683572402119 69465557075057525358603179)
  ·
    refine ⟨104198335612586288037904769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69465557075057525358603179 104198335612586288037904769)
    ·
      refine ⟨78148751709439716028428577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104198335612586288037904769 78148751709439716028428577)
      ·
        refine ⟨58611563782079787021321433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78148751709439716028428577 58611563782079787021321433)
        ·
          refine ⟨43958672836559840265991075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58611563782079787021321433 43958672836559840265991075)
          ·
            refine ⟨65938009254839760398986613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43958672836559840265991075 65938009254839760398986613)
            ·
              refine ⟨6181688367641227537404995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65938009254839760398986613 6181688367641227537404995)
              ·
                refine ⟨9272532551461841306107493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181688367641227537404995 9272532551461841306107493)
                ·
                  refine ⟨1738599853399095244895155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9272532551461841306107493 1738599853399095244895155)
                  ·
                    refine ⟨2607899780098642867342733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1738599853399095244895155 2607899780098642867342733)
                    ·
                      refine ⟨977962417536991075253525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2607899780098642867342733 977962417536991075253525)
                      ·
                        rfl

theorem cell23_1904575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_1904575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904575 prefixEnd_1904575 := by exact prefixLift 1904575
  have htrace : WordTrace (prefixWord ++ tailWord_1904575) baseStart_1904575 baseEnd_1904575 := by
    simpa [prefixWord, tailWord_1904575, baseEnd_1904575] using wordTrace_append hprefix tailTrace_1904575
  have hstable : (prefixWord ++ tailWord_1904575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904575).length < 2 ^ (prefixWord ++ tailWord_1904575).sum := by decide
  have hdescent : baseEnd_1904575 < baseStart_1904575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904610 : List Nat := [3, 3, 3, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1904610 : Nat := 118140960795 + 1904610 * 2 ^ 59
def prefixEnd_1904610 : Nat := 4983230072969 + 3 ^ 40 * 1904610 * 2
def baseEnd_1904610 : Nat := 977980389359898438315865

theorem tailTrace_1904610 : CollatzResearch.WordTrace tailWord_1904610 prefixEnd_1904610 977980389359898438315865 := by
  unfold tailWord_1904610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17366708407482681584031821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46311222419953817557418189 17366708407482681584031821)
  ·
    refine ⟨6512515652806005594011933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17366708407482681584031821 6512515652806005594011933)
    ·
      refine ⟨2442193369802252097754475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6512515652806005594011933 2442193369802252097754475)
      ·
        refine ⟨3663290054703378146631713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442193369802252097754475 3663290054703378146631713)
        ·
          refine ⟨2747467541027533609973785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663290054703378146631713 2747467541027533609973785)
          ·
            refine ⟨2060600655770650207480339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2747467541027533609973785 2060600655770650207480339)
            ·
              refine ⟨3090900983655975311220509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060600655770650207480339 3090900983655975311220509)
              ·
                refine ⟨1159087868870990741707691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3090900983655975311220509 1159087868870990741707691)
                ·
                  refine ⟨1738631803306486112561537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159087868870990741707691 1738631803306486112561537)
                  ·
                    refine ⟨1303973852479864584421153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738631803306486112561537 1303973852479864584421153)
                    ·
                      refine ⟨977980389359898438315865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303973852479864584421153 977980389359898438315865)
                      ·
                        rfl

theorem cell23_1904610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1904610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904610 prefixEnd_1904610 := by exact prefixLift 1904610
  have htrace : WordTrace (prefixWord ++ tailWord_1904610) baseStart_1904610 baseEnd_1904610 := by
    simpa [prefixWord, tailWord_1904610, baseEnd_1904610] using wordTrace_append hprefix tailTrace_1904610
  have hstable : (prefixWord ++ tailWord_1904610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904610).length < 2 ^ (prefixWord ++ tailWord_1904610).sum := by decide
  have hdescent : baseEnd_1904610 < baseStart_1904610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904632 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 4, 2, 2]
def baseStart_1904632 : Nat := 118140960795 + 1904632 * 2 ^ 59
def prefixEnd_1904632 : Nat := 4983230072969 + 3 ^ 40 * 1904632 * 2
def baseEnd_1904632 : Nat := 977991685934297352240763

theorem tailTrace_1904632 : CollatzResearch.WordTrace tailWord_1904632 prefixEnd_1904632 977991685934297352240763 := by
  unfold tailWord_1904632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733818017925512046714075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46311757357234016062285433 34733818017925512046714075)
  ·
    refine ⟨52100727026888268070071113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34733818017925512046714075 52100727026888268070071113)
    ·
      refine ⟨39075545270166201052553335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52100727026888268070071113 39075545270166201052553335)
      ·
        refine ⟨58613317905249301578830003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39075545270166201052553335 58613317905249301578830003)
        ·
          refine ⟨87919976857873952368245005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58613317905249301578830003 87919976857873952368245005)
          ·
            refine ⟨32969991321702732138091877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87919976857873952368245005 32969991321702732138091877)
            ·
              refine ⟨6181873372819262275892227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32969991321702732138091877 6181873372819262275892227)
              ·
                refine ⟨9272810059228893413838341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181873372819262275892227 9272810059228893413838341)
                ·
                  refine ⟨1738651886105417515094689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9272810059228893413838341 1738651886105417515094689)
                  ·
                    refine ⟨1303988914579063136321017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738651886105417515094689 1303988914579063136321017)
                    ·
                      refine ⟨977991685934297352240763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303988914579063136321017 977991685934297352240763)
                      ·
                        rfl

theorem cell23_1904632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_1904632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904632 prefixEnd_1904632 := by exact prefixLift 1904632
  have htrace : WordTrace (prefixWord ++ tailWord_1904632) baseStart_1904632 baseEnd_1904632 := by
    simpa [prefixWord, tailWord_1904632, baseEnd_1904632] using wordTrace_append hprefix tailTrace_1904632
  have hstable : (prefixWord ++ tailWord_1904632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904632).length < 2 ^ (prefixWord ++ tailWord_1904632).sum := by decide
  have hdescent : baseEnd_1904632 < baseStart_1904632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904653 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1904653 : Nat := 118140960795 + 1904653 * 2 ^ 59
def prefixEnd_1904653 : Nat := 4983230072969 + 3 ^ 40 * 1904653 * 2
def baseEnd_1904653 : Nat := 978002469028041770078167

theorem tailTrace_1904653 : CollatzResearch.WordTrace tailWord_1904653 prefixEnd_1904653 978002469028041770078167 := by
  unfold tailWord_1904653
  simp only [CollatzResearch.WordTrace]
  refine ⟨69468401968774944679942613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46312267979183296453295075 69468401968774944679942613)
  ·
    refine ⟨1628165671143162765936155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69468401968774944679942613 1628165671143162765936155)
    ·
      refine ⟨2442248506714744148904233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628165671143162765936155 2442248506714744148904233)
      ·
        refine ⟨1831686380036058111678175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2442248506714744148904233 1831686380036058111678175)
        ·
          refine ⟨2747529570054087167517263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831686380036058111678175 2747529570054087167517263)
          ·
            refine ⟨4121294355081130751275895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747529570054087167517263 4121294355081130751275895)
            ·
              refine ⟨6181941532621696126913843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121294355081130751275895 6181941532621696126913843)
              ·
                refine ⟨9272912298932544190370765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181941532621696126913843 9272912298932544190370765)
                ·
                  refine ⟨3477342112099704071389037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9272912298932544190370765 3477342112099704071389037)
                  ·
                    refine ⟨1304003292037389026770889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477342112099704071389037 1304003292037389026770889)
                    ·
                      refine ⟨978002469028041770078167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304003292037389026770889 978002469028041770078167)
                      ·
                        rfl

theorem cell23_1904653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1904653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904653 prefixEnd_1904653 := by exact prefixLift 1904653
  have htrace : WordTrace (prefixWord ++ tailWord_1904653) baseStart_1904653 baseEnd_1904653 := by
    simpa [prefixWord, tailWord_1904653, baseEnd_1904653] using wordTrace_append hprefix tailTrace_1904653
  have hstable : (prefixWord ++ tailWord_1904653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904653).length < 2 ^ (prefixWord ++ tailWord_1904653).sum := by decide
  have hdescent : baseEnd_1904653 < baseStart_1904653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904689 : List Nat := [1, 2, 2, 3, 1, 5, 2, 2, 5]
def baseStart_1904689 : Nat := 118140960795 + 1904689 * 2 ^ 59
def prefixEnd_1904689 : Nat := 4983230072969 + 3 ^ 40 * 1904689 * 2
def baseEnd_1904689 : Nat := 108668994925733736580889

theorem tailTrace_1904689 : CollatzResearch.WordTrace tailWord_1904689 prefixEnd_1904689 108668994925733736580889 := by
  unfold tailWord_1904689
  simp only [CollatzResearch.WordTrace]
  refine ⟨69469714996644522828253121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46313143331096348552168747 69469714996644522828253121)
  ·
    refine ⟨52102286247483392121189841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69469714996644522828253121 52102286247483392121189841)
    ·
      refine ⟨39076714685612544090892381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52102286247483392121189841 39076714685612544090892381)
      ·
        refine ⟨14653768007104704034084643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39076714685612544090892381 14653768007104704034084643)
        ·
          refine ⟨21980652010657056051126965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14653768007104704034084643 21980652010657056051126965)
          ·
            refine ⟨2060686125999099004793153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21980652010657056051126965 2060686125999099004793153)
            ·
              refine ⟨1545514594499324253594865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060686125999099004793153 1545514594499324253594865)
              ·
                refine ⟨1159135945874493190196149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545514594499324253594865 1159135945874493190196149)
                ·
                  refine ⟨108668994925733736580889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1159135945874493190196149 108668994925733736580889)
                  ·
                    rfl

theorem cell23_1904689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 5].length) (baseStart_1904689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904689 prefixEnd_1904689 := by exact prefixLift 1904689
  have htrace : WordTrace (prefixWord ++ tailWord_1904689) baseStart_1904689 baseEnd_1904689 := by
    simpa [prefixWord, tailWord_1904689, baseEnd_1904689] using wordTrace_append hprefix tailTrace_1904689
  have hstable : (prefixWord ++ tailWord_1904689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904689).length < 2 ^ (prefixWord ++ tailWord_1904689).sum := by decide
  have hdescent : baseEnd_1904689 < baseStart_1904689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904698 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_1904698 : Nat := 118140960795 + 1904698 * 2 ^ 59
def prefixEnd_1904698 : Nat := 4983230072969 + 3 ^ 40 * 1904698 * 2
def baseEnd_1904698 : Nat := 326008525219164698005153

theorem tailTrace_1904698 : CollatzResearch.WordTrace tailWord_1904698 prefixEnd_1904698 326008525219164698005153 := by
  unfold tailWord_1904698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367510813402979341332687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46313362169074611576887165 17367510813402979341332687)
  ·
    refine ⟨26051266220104469011999031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17367510813402979341332687 26051266220104469011999031)
    ·
      refine ⟨39076899330156703517998547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26051266220104469011999031 39076899330156703517998547)
      ·
        refine ⟨58615348995235055276997821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39076899330156703517998547 58615348995235055276997821)
        ·
          refine ⟨21980755873213145728874183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58615348995235055276997821 21980755873213145728874183)
          ·
            refine ⟨32971133809819718593311275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21980755873213145728874183 32971133809819718593311275)
            ·
              refine ⟨49456700714729577889966913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32971133809819718593311275 49456700714729577889966913)
              ·
                refine ⟨37092525536047183417475185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49456700714729577889966913 37092525536047183417475185)
                ·
                  refine ⟨27819394152035387563106389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37092525536047183417475185 27819394152035387563106389)
                  ·
                    refine ⟨326008525219164698005153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27819394152035387563106389 326008525219164698005153)
                    ·
                      rfl

theorem cell23_1904698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_1904698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904698 prefixEnd_1904698 := by exact prefixLift 1904698
  have htrace : WordTrace (prefixWord ++ tailWord_1904698) baseStart_1904698 baseEnd_1904698 := by
    simpa [prefixWord, tailWord_1904698, baseEnd_1904698] using wordTrace_append hprefix tailTrace_1904698
  have hstable : (prefixWord ++ tailWord_1904698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904698).length < 2 ^ (prefixWord ++ tailWord_1904698).sum := by decide
  have hdescent : baseEnd_1904698 < baseStart_1904698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904715 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 3, 4]
def baseStart_1904715 : Nat := 118140960795 + 1904715 * 2 ^ 59
def prefixEnd_1904715 : Nat := 4983230072969 + 3 ^ 40 * 1904715 * 2
def baseEnd_1904715 : Nat := 326011434942873509167627

theorem tailTrace_1904715 : CollatzResearch.WordTrace tailWord_1904715 prefixEnd_1904715 326011434942873509167627 := by
  unfold tailWord_1904715
  simp only [CollatzResearch.WordTrace]
  refine ⟨69470663294550329268699599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46313775529700219512466399 69470663294550329268699599)
  ·
    refine ⟨104205994941825493903049399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69470663294550329268699599 104205994941825493903049399)
    ·
      refine ⟨156308992412738240854574099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104205994941825493903049399 156308992412738240854574099)
      ·
        refine ⟨234463488619107361281861149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156308992412738240854574099 234463488619107361281861149)
        ·
          refine ⟨87923808232165260480697931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234463488619107361281861149 87923808232165260480697931)
          ·
            refine ⟨131885712348247890721046897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87923808232165260480697931 131885712348247890721046897)
            ·
              refine ⟨98914284261185918040785173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131885712348247890721046897 98914284261185918040785173)
              ·
                refine ⟨4636607074743089908161805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98914284261185918040785173 4636607074743089908161805)
                ·
                  refine ⟨1738727653028658715560677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4636607074743089908161805 1738727653028658715560677)
                  ·
                    refine ⟨326011434942873509167627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1738727653028658715560677 326011434942873509167627)
                    ·
                      rfl

theorem cell23_1904715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 4].length) (baseStart_1904715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904715 prefixEnd_1904715 := by exact prefixLift 1904715
  have htrace : WordTrace (prefixWord ++ tailWord_1904715) baseStart_1904715 baseEnd_1904715 := by
    simpa [prefixWord, tailWord_1904715, baseEnd_1904715] using wordTrace_append hprefix tailTrace_1904715
  have hstable : (prefixWord ++ tailWord_1904715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904715).length < 2 ^ (prefixWord ++ tailWord_1904715).sum := by decide
  have hdescent : baseEnd_1904715 < baseStart_1904715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904722 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1904722 : Nat := 118140960795 + 1904722 * 2 ^ 59
def prefixEnd_1904722 : Nat := 4983230072969 + 3 ^ 40 * 1904722 * 2
def baseEnd_1904722 : Nat := 978037899193202000115349

theorem tailTrace_1904722 : CollatzResearch.WordTrace tailWord_1904722 prefixEnd_1904722 978037899193202000115349 := by
  unfold tailWord_1904722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367729651381242366051105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46313945737016646309469613 17367729651381242366051105)
  ·
    refine ⟨13025797238535931774538329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17367729651381242366051105 13025797238535931774538329)
    ·
      refine ⟨9769347928901948830903747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13025797238535931774538329 9769347928901948830903747)
      ·
        refine ⟨14654021893352923246355621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9769347928901948830903747 14654021893352923246355621)
        ·
          refine ⟨2747629105003673108691679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14654021893352923246355621 2747629105003673108691679)
          ·
            refine ⟨4121443657505509663037519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747629105003673108691679 4121443657505509663037519)
            ·
              refine ⟨6182165486258264494556279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121443657505509663037519 6182165486258264494556279)
              ·
                refine ⟨9273248229387396741834419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6182165486258264494556279 9273248229387396741834419)
                ·
                  refine ⟨13909872344081095112751629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9273248229387396741834419 13909872344081095112751629)
                  ·
                    refine ⟨5216202129030410667281861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13909872344081095112751629 5216202129030410667281861)
                    ·
                      refine ⟨978037899193202000115349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5216202129030410667281861 978037899193202000115349)
                      ·
                        rfl

theorem cell23_1904722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1904722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904722 prefixEnd_1904722 := by exact prefixLift 1904722
  have htrace : WordTrace (prefixWord ++ tailWord_1904722) baseStart_1904722 baseEnd_1904722 := by
    simpa [prefixWord, tailWord_1904722, baseEnd_1904722] using wordTrace_append hprefix tailTrace_1904722
  have hstable : (prefixWord ++ tailWord_1904722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904722).length < 2 ^ (prefixWord ++ tailWord_1904722).sum := by decide
  have hdescent : baseEnd_1904722 < baseStart_1904722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904749 : List Nat := [1, 5, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1904749 : Nat := 118140960795 + 1904749 * 2 ^ 59
def prefixEnd_1904749 : Nat := 4983230072969 + 3 ^ 40 * 1904749 * 2
def baseEnd_1904749 : Nat := 326017254390291131492575

theorem tailTrace_1904749 : CollatzResearch.WordTrace tailWord_1904749 prefixEnd_1904749 326017254390291131492575 := by
  unfold tailWord_1904749
  simp only [CollatzResearch.WordTrace]
  refine ⟨69471903376427153075437301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46314602250951435383624867 69471903376427153075437301)
  ·
    refine ⟨6512990941540045600822247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69471903376427153075437301 6512990941540045600822247)
    ·
      refine ⟨9769486412310068401233371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512990941540045600822247 9769486412310068401233371)
      ·
        refine ⟨14654229618465102601850057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9769486412310068401233371 14654229618465102601850057)
        ·
          refine ⟨10990672213848826951387543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14654229618465102601850057 10990672213848826951387543)
          ·
            refine ⟨16486008320773240427081315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990672213848826951387543 16486008320773240427081315)
            ·
              refine ⟨24729012481159860640621973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16486008320773240427081315 24729012481159860640621973)
              ·
                refine ⟨1159172460054368467529155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24729012481159860640621973 1159172460054368467529155)
                ·
                  refine ⟨1738758690081552701293733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159172460054368467529155 1738758690081552701293733)
                  ·
                    refine ⟨326017254390291131492575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1738758690081552701293733 326017254390291131492575)
                    ·
                      rfl

theorem cell23_1904749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1904749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904749 prefixEnd_1904749 := by exact prefixLift 1904749
  have htrace : WordTrace (prefixWord ++ tailWord_1904749) baseStart_1904749 baseEnd_1904749 := by
    simpa [prefixWord, tailWord_1904749, baseEnd_1904749] using wordTrace_append hprefix tailTrace_1904749
  have hstable : (prefixWord ++ tailWord_1904749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904749).length < 2 ^ (prefixWord ++ tailWord_1904749).sum := by decide
  have hdescent : baseEnd_1904749 < baseStart_1904749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904775 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 3, 5]
def baseStart_1904775 : Nat := 118140960795 + 1904775 * 2 ^ 59
def prefixEnd_1904775 : Nat := 4983230072969 + 3 ^ 40 * 1904775 * 2
def baseEnd_1904775 : Nat := 326021704555963430917535

theorem tailTrace_1904775 : CollatzResearch.WordTrace tailWord_1904775 prefixEnd_1904775 326021704555963430917535 := by
  unfold tailWord_1904775
  simp only [CollatzResearch.WordTrace]
  refine ⟨69472851674332959515883779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46315234449555306343922519 69472851674332959515883779)
  ·
    refine ⟨104209277511499439273825669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69472851674332959515883779 104209277511499439273825669)
    ·
      refine ⟨19539239533406144863842313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104209277511499439273825669 19539239533406144863842313)
      ·
        refine ⟨14654429650054608647881735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19539239533406144863842313 14654429650054608647881735)
        ·
          refine ⟨21981644475081912971822603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654429650054608647881735 21981644475081912971822603)
          ·
            refine ⟨32972466712622869457733905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21981644475081912971822603 32972466712622869457733905)
            ·
              refine ⟨24729350034467152093300429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32972466712622869457733905 24729350034467152093300429)
              ·
                refine ⟨9273506262925182034987661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24729350034467152093300429 9273506262925182034987661)
                ·
                  refine ⟨3477564848596943263120373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9273506262925182034987661 3477564848596943263120373)
                  ·
                    refine ⟨326021704555963430917535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3477564848596943263120373 326021704555963430917535)
                    ·
                      rfl

theorem cell23_1904775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_1904775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904775 prefixEnd_1904775 := by exact prefixLift 1904775
  have htrace : WordTrace (prefixWord ++ tailWord_1904775) baseStart_1904775 baseEnd_1904775 := by
    simpa [prefixWord, tailWord_1904775, baseEnd_1904775] using wordTrace_append hprefix tailTrace_1904775
  have hstable : (prefixWord ++ tailWord_1904775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904775).length < 2 ^ (prefixWord ++ tailWord_1904775).sum := by decide
  have hdescent : baseEnd_1904775 < baseStart_1904775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904790 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1904790 : Nat := 118140960795 + 1904790 * 2 ^ 59
def prefixEnd_1904790 : Nat := 4983230072969 + 3 ^ 40 * 1904790 * 2
def baseEnd_1904790 : Nat := 978072815877707734065037

theorem tailTrace_1904790 : CollatzResearch.WordTrace tailWord_1904790 prefixEnd_1904790 978072815877707734065037 := by
  unfold tailWord_1904790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4342087423079913567354989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46315599179519078051786549 4342087423079913567354989)
  ·
    refine ⟨1628282783654967587758121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4342087423079913567354989 1628282783654967587758121)
    ·
      refine ⟨1221212087741225690818591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1628282783654967587758121 1221212087741225690818591)
      ·
        refine ⟨1831818131611838536227887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221212087741225690818591 1831818131611838536227887)
        ·
          refine ⟨2747727197417757804341831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831818131611838536227887 2747727197417757804341831)
          ·
            refine ⟨4121590796126636706512747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747727197417757804341831 4121590796126636706512747)
            ·
              refine ⟨6182386194189955059769121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121590796126636706512747 6182386194189955059769121)
              ·
                refine ⟨4636789645642466294826841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182386194189955059769121 4636789645642466294826841)
                ·
                  refine ⟨3477592234231849721120131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636789645642466294826841 3477592234231849721120131)
                  ·
                    refine ⟨5216388351347774581680197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3477592234231849721120131 5216388351347774581680197)
                    ·
                      refine ⟨978072815877707734065037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5216388351347774581680197 978072815877707734065037)
                      ·
                        rfl

theorem cell23_1904790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1904790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904790 prefixEnd_1904790 := by exact prefixLift 1904790
  have htrace : WordTrace (prefixWord ++ tailWord_1904790) baseStart_1904790 baseEnd_1904790 := by
    simpa [prefixWord, tailWord_1904790, baseEnd_1904790] using wordTrace_append hprefix tailTrace_1904790
  have hstable : (prefixWord ++ tailWord_1904790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904790).length < 2 ^ (prefixWord ++ tailWord_1904790).sum := by decide
  have hdescent : baseEnd_1904790 < baseStart_1904790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904799 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1904799 : Nat := 118140960795 + 1904799 * 2 ^ 59
def prefixEnd_1904799 : Nat := 4983230072969 + 3 ^ 40 * 1904799 * 2
def baseEnd_1904799 : Nat := 978077437203598198852495

theorem tailTrace_1904799 : CollatzResearch.WordTrace tailWord_1904799 prefixEnd_1904799 978077437203598198852495 := by
  unfold tailWord_1904799
  simp only [CollatzResearch.WordTrace]
  refine ⟨69473727026246011614757451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46315818017497341076504967 69473727026246011614757451)
  ·
    refine ⟨104210590539369017422136177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69473727026246011614757451 104210590539369017422136177)
    ·
      refine ⟨78157942904526763066602133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104210590539369017422136177 78157942904526763066602133)
      ·
        refine ⟨3663653573649692018746975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78157942904526763066602133 3663653573649692018746975)
        ·
          refine ⟨5495480360474538028120463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663653573649692018746975 5495480360474538028120463)
          ·
            refine ⟨8243220540711807042180695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5495480360474538028120463 8243220540711807042180695)
            ·
              refine ⟨12364830811067710563271043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243220540711807042180695 12364830811067710563271043)
              ·
                refine ⟨18547246216601565844906565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364830811067710563271043 18547246216601565844906565)
                ·
                  refine ⟨3477608665612793595919981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18547246216601565844906565 3477608665612793595919981)
                  ·
                    refine ⟨1304103249604797598469993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477608665612793595919981 1304103249604797598469993)
                    ·
                      refine ⟨978077437203598198852495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304103249604797598469993 978077437203598198852495)
                      ·
                        rfl

theorem cell23_1904799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1904799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904799 prefixEnd_1904799 := by exact prefixLift 1904799
  have htrace : WordTrace (prefixWord ++ tailWord_1904799) baseStart_1904799 baseEnd_1904799 := by
    simpa [prefixWord, tailWord_1904799, baseEnd_1904799] using wordTrace_append hprefix tailTrace_1904799
  have hstable : (prefixWord ++ tailWord_1904799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904799).length < 2 ^ (prefixWord ++ tailWord_1904799).sum := by decide
  have hdescent : baseEnd_1904799 < baseStart_1904799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904815 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 3]
def baseStart_1904815 : Nat := 118140960795 + 1904815 * 2 ^ 59
def prefixEnd_1904815 : Nat := 4983230072969 + 3 ^ 40 * 1904815 * 2
def baseEnd_1904815 : Nat := 978085652894070136252421

theorem tailTrace_1904815 : CollatzResearch.WordTrace tailWord_1904815 prefixEnd_1904815 978085652894070136252421 := by
  unfold tailWord_1904815
  simp only [CollatzResearch.WordTrace]
  refine ⟨69474310594188046347339899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46316207062792030898226599 69474310594188046347339899)
  ·
    refine ⟨104211465891282069521009849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69474310594188046347339899 104211465891282069521009849)
    ·
      refine ⟨78158599418461552140757387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104211465891282069521009849 78158599418461552140757387)
      ·
        refine ⟨117237899127692328211136081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78158599418461552140757387 117237899127692328211136081)
        ·
          refine ⟨87928424345769246158352061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117237899127692328211136081 87928424345769246158352061)
          ·
            refine ⟨32973159129663467309382023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87928424345769246158352061 32973159129663467309382023)
            ·
              refine ⟨49459738694495200964073035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32973159129663467309382023 49459738694495200964073035)
              ·
                refine ⟨74189608041742801446109553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49459738694495200964073035 74189608041742801446109553)
                ·
                  refine ⟨55642206031307101084582165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74189608041742801446109553 55642206031307101084582165)
                  ·
                    refine ⟨2608228407717520363339789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55642206031307101084582165 2608228407717520363339789)
                    ·
                      refine ⟨978085652894070136252421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2608228407717520363339789 978085652894070136252421)
                      ·
                        rfl

theorem cell23_1904815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_1904815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904815 prefixEnd_1904815 := by exact prefixLift 1904815
  have htrace : WordTrace (prefixWord ++ tailWord_1904815) baseStart_1904815 baseEnd_1904815 := by
    simpa [prefixWord, tailWord_1904815, baseEnd_1904815] using wordTrace_append hprefix tailTrace_1904815
  have hstable : (prefixWord ++ tailWord_1904815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904815).length < 2 ^ (prefixWord ++ tailWord_1904815).sum := by decide
  have hdescent : baseEnd_1904815 < baseStart_1904815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904825 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1904825 : Nat := 118140960795 + 1904825 * 2 ^ 59
def prefixEnd_1904825 : Nat := 4983230072969 + 3 ^ 40 * 1904825 * 2
def baseEnd_1904825 : Nat := 978090787700615097127375

theorem tailTrace_1904825 : CollatzResearch.WordTrace tailWord_1904825 prefixEnd_1904825 978090787700615097127375 := by
  unfold tailWord_1904825
  simp only [CollatzResearch.WordTrace]
  refine ⟨69474675324151818055203929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46316450216101212036802619 69474675324151818055203929)
  ·
    refine ⟨52106006493113863541402947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69474675324151818055203929 52106006493113863541402947)
    ·
      refine ⟨78159009739670795312104421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52106006493113863541402947 78159009739670795312104421)
      ·
        refine ⟨14654814326188274121019579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78159009739670795312104421 14654814326188274121019579)
        ·
          refine ⟨21982221489282411181529369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654814326188274121019579 21982221489282411181529369)
          ·
            refine ⟨16486666116961808386147027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21982221489282411181529369 16486666116961808386147027)
            ·
              refine ⟨24729999175442712579220541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16486666116961808386147027 24729999175442712579220541)
              ·
                refine ⟨9273749690791017217207703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24729999175442712579220541 9273749690791017217207703)
                ·
                  refine ⟨13910624536186525825811555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9273749690791017217207703 13910624536186525825811555)
                  ·
                    refine ⟨20865936804279788738717333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13910624536186525825811555 20865936804279788738717333)
                    ·
                      refine ⟨978090787700615097127375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20865936804279788738717333 978090787700615097127375)
                      ·
                        rfl

theorem cell23_1904825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1904825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904825 prefixEnd_1904825 := by exact prefixLift 1904825
  have htrace : WordTrace (prefixWord ++ tailWord_1904825) baseStart_1904825 baseEnd_1904825 := by
    simpa [prefixWord, tailWord_1904825, baseEnd_1904825] using wordTrace_append hprefix tailTrace_1904825
  have hstable : (prefixWord ++ tailWord_1904825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904825).length < 2 ^ (prefixWord ++ tailWord_1904825).sum := by decide
  have hdescent : baseEnd_1904825 < baseStart_1904825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904829 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_1904829 : Nat := 118140960795 + 1904829 * 2 ^ 59
def prefixEnd_1904829 : Nat := 4983230072969 + 3 ^ 40 * 1904829 * 2
def baseEnd_1904829 : Nat := 978092841623233081477357

theorem tailTrace_1904829 : CollatzResearch.WordTrace tailWord_1904829 prefixEnd_1904829 978092841623233081477357 := by
  unfold tailWord_1904829
  simp only [CollatzResearch.WordTrace]
  refine ⟨69474821216137326738349541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46316547477424884492233027 69474821216137326738349541)
  ·
    refine ⟨13026528978025748763440539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69474821216137326738349541 13026528978025748763440539)
    ·
      refine ⟨19539793467038623145160809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026528978025748763440539 19539793467038623145160809)
      ·
        refine ⟨14654845100278967358870607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19539793467038623145160809 14654845100278967358870607)
        ·
          refine ⟨21982267650418451038305911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654845100278967358870607 21982267650418451038305911)
          ·
            refine ⟨32973401475627676557458867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21982267650418451038305911 32973401475627676557458867)
            ·
              refine ⟨49460102213441514836188301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32973401475627676557458867 49460102213441514836188301)
              ·
                refine ⟨18547538330040568063570613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49460102213441514836188301 18547538330040568063570613)
                ·
                  refine ⟨1738831718441303255959745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18547538330040568063570613 1738831718441303255959745)
                  ·
                    refine ⟨1304123788830977441969809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738831718441303255959745 1304123788830977441969809)
                    ·
                      refine ⟨978092841623233081477357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304123788830977441969809 978092841623233081477357)
                      ·
                        rfl

theorem cell23_1904829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_1904829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904829 prefixEnd_1904829 := by exact prefixLift 1904829
  have htrace : WordTrace (prefixWord ++ tailWord_1904829) baseStart_1904829 baseEnd_1904829 := by
    simpa [prefixWord, tailWord_1904829, baseEnd_1904829] using wordTrace_append hprefix tailTrace_1904829
  have hstable : (prefixWord ++ tailWord_1904829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904829).length < 2 ^ (prefixWord ++ tailWord_1904829).sum := by decide
  have hdescent : baseEnd_1904829 < baseStart_1904829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904833 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1904833 : Nat := 118140960795 + 1904833 * 2 ^ 59
def prefixEnd_1904833 : Nat := 4983230072969 + 3 ^ 40 * 1904833 * 2
def baseEnd_1904833 : Nat := 978094895545851065827339

theorem tailTrace_1904833 : CollatzResearch.WordTrace tailWord_1904833 prefixEnd_1904833 978094895545851065827339 := by
  unfold tailWord_1904833
  simp only [CollatzResearch.WordTrace]
  refine ⟨69474967108122835421495153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46316644738748556947663435 69474967108122835421495153)
  ·
    refine ⟨52106225331092126566121365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69474967108122835421495153 52106225331092126566121365)
    ·
      refine ⟨2442479312394943432786939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52106225331092126566121365 2442479312394943432786939)
      ·
        refine ⟨3663718968592415149180409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442479312394943432786939 3663718968592415149180409)
        ·
          refine ⟨2747789226444311361885307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663718968592415149180409 2747789226444311361885307)
          ·
            refine ⟨4121683839666467042827961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747789226444311361885307 4121683839666467042827961)
            ·
              refine ⟨3091262879749850282120971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4121683839666467042827961 3091262879749850282120971)
              ·
                refine ⟨4636894319624775423181457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091262879749850282120971 4636894319624775423181457)
                ·
                  refine ⟨3477670739718581567386093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636894319624775423181457 3477670739718581567386093)
                  ·
                    refine ⟨1304126527394468087769785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477670739718581567386093 1304126527394468087769785)
                    ·
                      refine ⟨978094895545851065827339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304126527394468087769785 978094895545851065827339)
                      ·
                        rfl

theorem cell23_1904833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1904833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904833 prefixEnd_1904833 := by exact prefixLift 1904833
  have htrace : WordTrace (prefixWord ++ tailWord_1904833) baseStart_1904833 baseEnd_1904833 := by
    simpa [prefixWord, tailWord_1904833, baseEnd_1904833] using wordTrace_append hprefix tailTrace_1904833
  have hstable : (prefixWord ++ tailWord_1904833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904833).length < 2 ^ (prefixWord ++ tailWord_1904833).sum := by decide
  have hdescent : baseEnd_1904833 < baseStart_1904833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904842 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_1904842 : Nat := 118140960795 + 1904842 * 2 ^ 59
def prefixEnd_1904842 : Nat := 4983230072969 + 3 ^ 40 * 1904842 * 2
def baseEnd_1904842 : Nat := 978099516871741530614797

theorem tailTrace_1904842 : CollatzResearch.WordTrace tailWord_1904842 prefixEnd_1904842 978099516871741530614797 := by
  unfold tailWord_1904842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17368823841272557489643195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46316863576726819972381853 17368823841272557489643195)
  ·
    refine ⟨26053235761908836234464793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17368823841272557489643195 26053235761908836234464793)
    ·
      refine ⟨19539926821431627175848595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26053235761908836234464793 19539926821431627175848595)
      ·
        refine ⟨29309890232147440763772893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19539926821431627175848595 29309890232147440763772893)
        ·
          refine ⟨10991208837055290286414835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29309890232147440763772893 10991208837055290286414835)
          ·
            refine ⟨16486813255582935429622253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10991208837055290286414835 16486813255582935429622253)
            ·
              refine ⟨6182554970843600786108345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16486813255582935429622253 6182554970843600786108345)
              ·
                refine ⟨4636916228132700589581259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182554970843600786108345 4636916228132700589581259)
                ·
                  refine ⟨6955374342199050884371889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636916228132700589581259 6955374342199050884371889)
                  ·
                    refine ⟨5216530756649288163278917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6955374342199050884371889 5216530756649288163278917)
                    ·
                      refine ⟨978099516871741530614797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5216530756649288163278917 978099516871741530614797)
                      ·
                        rfl

theorem cell23_1904842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_1904842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904842 prefixEnd_1904842 := by exact prefixLift 1904842
  have htrace : WordTrace (prefixWord ++ tailWord_1904842) baseStart_1904842 baseEnd_1904842 := by
    simpa [prefixWord, tailWord_1904842, baseEnd_1904842] using wordTrace_append hprefix tailTrace_1904842
  have hstable : (prefixWord ++ tailWord_1904842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904842).length < 2 ^ (prefixWord ++ tailWord_1904842).sum := by decide
  have hdescent : baseEnd_1904842 < baseStart_1904842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904846 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_1904846 : Nat := 118140960795 + 1904846 * 2 ^ 59
def prefixEnd_1904846 : Nat := 4983230072969 + 3 ^ 40 * 1904846 * 2
def baseEnd_1904846 : Nat := 978101570794359514964779

theorem tailTrace_1904846 : CollatzResearch.WordTrace tailWord_1904846 prefixEnd_1904846 978101570794359514964779 := by
  unfold tailWord_1904846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8684430157134467330214799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46316960838050492427812261 8684430157134467330214799)
  ·
    refine ⟨13026645235701700995322199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8684430157134467330214799 13026645235701700995322199)
    ·
      refine ⟨19539967853552551492983299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026645235701700995322199 19539967853552551492983299)
      ·
        refine ⟨29309951780328827239474949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19539967853552551492983299 29309951780328827239474949)
        ·
          refine ⟨5495615958811655107401553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29309951780328827239474949 5495615958811655107401553)
          ·
            refine ⟨4121711969108741330551165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5495615958811655107401553 4121711969108741330551165)
            ·
              refine ⟨1545641988415777998956687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4121711969108741330551165 1545641988415777998956687)
              ·
                refine ⟨2318462982623666998435031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545641988415777998956687 2318462982623666998435031)
                ·
                  refine ⟨3477694473935500497652547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318462982623666998435031 3477694473935500497652547)
                  ·
                    refine ⟨5216541710903250746478821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3477694473935500497652547 5216541710903250746478821)
                    ·
                      refine ⟨978101570794359514964779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5216541710903250746478821 978101570794359514964779)
                      ·
                        rfl

theorem cell23_1904846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_1904846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904846 prefixEnd_1904846 := by exact prefixLift 1904846
  have htrace : WordTrace (prefixWord ++ tailWord_1904846) baseStart_1904846 baseEnd_1904846 := by
    simpa [prefixWord, tailWord_1904846, baseEnd_1904846] using wordTrace_append hprefix tailTrace_1904846
  have hstable : (prefixWord ++ tailWord_1904846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904846).length < 2 ^ (prefixWord ++ tailWord_1904846).sum := by decide
  have hdescent : baseEnd_1904846 < baseStart_1904846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904865 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 9]
def baseStart_1904865 : Nat := 118140960795 + 1904865 * 2 ^ 59
def prefixEnd_1904865 : Nat := 4983230072969 + 3 ^ 40 * 1904865 * 2
def baseEnd_1904865 : Nat := 326037108975598313542397

theorem tailTrace_1904865 : CollatzResearch.WordTrace tailWord_1904865 prefixEnd_1904865 326037108975598313542397 := by
  unfold tailWord_1904865
  simp only [CollatzResearch.WordTrace]
  refine ⟨69476134244006904886660049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46317422829337936591106699 69476134244006904886660049)
  ·
    refine ⟨52107100683005178664995037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69476134244006904886660049 52107100683005178664995037)
    ·
      refine ⟨19540162756126941999373139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52107100683005178664995037 19540162756126941999373139)
      ·
        refine ⟨29310244134190412999059709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19540162756126941999373139 29310244134190412999059709)
        ·
          refine ⟨10991341550321404874647391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29310244134190412999059709 10991341550321404874647391)
          ·
            refine ⟨16487012325482107311971087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10991341550321404874647391 16487012325482107311971087)
            ·
              refine ⟨24730518488223160967956631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16487012325482107311971087 24730518488223160967956631)
              ·
                refine ⟨37095777732334741451934947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24730518488223160967956631 37095777732334741451934947)
                ·
                  refine ⟨55643666598502112177902421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37095777732334741451934947 55643666598502112177902421)
                  ·
                    refine ⟨326037108975598313542397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55643666598502112177902421 326037108975598313542397)
                    ·
                      rfl

theorem cell23_1904865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_1904865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904865 prefixEnd_1904865 := by exact prefixLift 1904865
  have htrace : WordTrace (prefixWord ++ tailWord_1904865) baseStart_1904865 baseEnd_1904865 := by
    simpa [prefixWord, tailWord_1904865, baseEnd_1904865] using wordTrace_append hprefix tailTrace_1904865
  have hstable : (prefixWord ++ tailWord_1904865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904865).length < 2 ^ (prefixWord ++ tailWord_1904865).sum := by decide
  have hdescent : baseEnd_1904865 < baseStart_1904865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904879 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 3]
def baseStart_1904879 : Nat := 118140960795 + 1904879 * 2 ^ 59
def prefixEnd_1904879 : Nat := 4983230072969 + 3 ^ 40 * 1904879 * 2
def baseEnd_1904879 : Nat := 978118515655957885852127

theorem tailTrace_1904879 : CollatzResearch.WordTrace tailWord_1904879 prefixEnd_1904879 978118515655957885852127 := by
  unfold tailWord_1904879
  simp only [CollatzResearch.WordTrace]
  refine ⟨69476644865956185277669691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46317763243970790185113127 69476644865956185277669691)
  ·
    refine ⟨104214967298934277916504537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69476644865956185277669691 104214967298934277916504537)
    ·
      refine ⟨78161225474200708437378403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104214967298934277916504537 78161225474200708437378403)
      ·
        refine ⟨117241838211301062656067605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78161225474200708437378403 117241838211301062656067605)
        ·
          refine ⟨5495711166154737312003169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117241838211301062656067605 5495711166154737312003169)
          ·
            refine ⟨4121783374616052984002377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5495711166154737312003169 4121783374616052984002377)
            ·
              refine ⟨3091337530962039738001783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4121783374616052984002377 3091337530962039738001783)
              ·
                refine ⟨4637006296443059607002675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091337530962039738001783 4637006296443059607002675)
                ·
                  refine ⟨6955509444664589410504013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637006296443059607002675 6955509444664589410504013)
                  ·
                    refine ⟨2608316041749221028939005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6955509444664589410504013 2608316041749221028939005)
                    ·
                      refine ⟨978118515655957885852127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2608316041749221028939005 978118515655957885852127)
                      ·
                        rfl

theorem cell23_1904879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_1904879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904879 prefixEnd_1904879 := by exact prefixLift 1904879
  have htrace : WordTrace (prefixWord ++ tailWord_1904879) baseStart_1904879 baseEnd_1904879 := by
    simpa [prefixWord, tailWord_1904879, baseEnd_1904879] using wordTrace_append hprefix tailTrace_1904879
  have hstable : (prefixWord ++ tailWord_1904879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904879).length < 2 ^ (prefixWord ++ tailWord_1904879).sum := by decide
  have hdescent : baseEnd_1904879 < baseStart_1904879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904895 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 1, 8]
def baseStart_1904895 : Nat := 118140960795 + 1904895 * 2 ^ 59
def prefixEnd_1904895 : Nat := 4983230072969 + 3 ^ 40 * 1904895 * 2
def baseEnd_1904895 : Nat := 326042243782143274417351

theorem tailTrace_1904895 : CollatzResearch.WordTrace tailWord_1904895 prefixEnd_1904895 326042243782143274417351 := by
  unfold tailWord_1904895
  simp only [CollatzResearch.WordTrace]
  refine ⟨69477228433898220010252139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46318152289265480006834759 69477228433898220010252139)
  ·
    refine ⟨104215842650847330015378209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69477228433898220010252139 104215842650847330015378209)
    ·
      refine ⟨78161881988135497511533657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104215842650847330015378209 78161881988135497511533657)
      ·
        refine ⟨58621411491101623133650243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78161881988135497511533657 58621411491101623133650243)
        ·
          refine ⟨87932117236652434700475365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58621411491101623133650243 87932117236652434700475365)
          ·
            refine ⟨16487271981872331506339131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87932117236652434700475365 16487271981872331506339131)
            ·
              refine ⟨24730907972808497259508697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16487271981872331506339131 24730907972808497259508697)
              ·
                refine ⟨18548180979606372944631523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24730907972808497259508697 18548180979606372944631523)
                ·
                  refine ⟨27822271469409559416947285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18548180979606372944631523 27822271469409559416947285)
                  ·
                    refine ⟨326042243782143274417351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27822271469409559416947285 326042243782143274417351)
                    ·
                      rfl

theorem cell23_1904895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_1904895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904895 prefixEnd_1904895 := by exact prefixLift 1904895
  have htrace : WordTrace (prefixWord ++ tailWord_1904895) baseStart_1904895 baseEnd_1904895 := by
    simpa [prefixWord, tailWord_1904895, baseEnd_1904895] using wordTrace_append hprefix tailTrace_1904895
  have hstable : (prefixWord ++ tailWord_1904895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904895).length < 2 ^ (prefixWord ++ tailWord_1904895).sum := by decide
  have hdescent : baseEnd_1904895 < baseStart_1904895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904900 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1904900 : Nat := 118140960795 + 1904900 * 2 ^ 59
def prefixEnd_1904900 : Nat := 4983230072969 + 3 ^ 40 * 1904900 * 2
def baseEnd_1904900 : Nat := 978129298749702303689531

theorem tailTrace_1904900 : CollatzResearch.WordTrace tailWord_1904900 prefixEnd_1904900 978129298749702303689531 := by
  unfold tailWord_1904900
  simp only [CollatzResearch.WordTrace]
  refine ⟨34738705399440052932092077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46318273865920070576122769 34738705399440052932092077)
  ·
    refine ⟨13027014524790019849534529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34738705399440052932092077 13027014524790019849534529)
    ·
      refine ⟨9770260893592514887150897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13027014524790019849534529 9770260893592514887150897)
      ·
        refine ⟨7327695670194386165363173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9770260893592514887150897 7327695670194386165363173)
        ·
          refine ⟨1373942938161447406005595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7327695670194386165363173 1373942938161447406005595)
          ·
            refine ⟨2060914407242171109008393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373942938161447406005595 2060914407242171109008393)
            ·
              refine ⟨1545685805431628331756295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060914407242171109008393 1545685805431628331756295)
              ·
                refine ⟨2318528708147442497634443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545685805431628331756295 2318528708147442497634443)
                ·
                  refine ⟨3477793062221163746451665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318528708147442497634443 3477793062221163746451665)
                  ·
                    refine ⟨2608344796665872809838749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3477793062221163746451665 2608344796665872809838749)
                    ·
                      refine ⟨978129298749702303689531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2608344796665872809838749 978129298749702303689531)
                      ·
                        rfl

theorem cell23_1904900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1904900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904900 prefixEnd_1904900 := by exact prefixLift 1904900
  have htrace : WordTrace (prefixWord ++ tailWord_1904900) baseStart_1904900 baseEnd_1904900 := by
    simpa [prefixWord, tailWord_1904900, baseEnd_1904900] using wordTrace_append hprefix tailTrace_1904900
  have hstable : (prefixWord ++ tailWord_1904900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904900).length < 2 ^ (prefixWord ++ tailWord_1904900).sum := by decide
  have hdescent : baseEnd_1904900 < baseStart_1904900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904952 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_1904952 : Nat := 118140960795 + 1904952 * 2 ^ 59
def prefixEnd_1904952 : Nat := 4983230072969 + 3 ^ 40 * 1904952 * 2
def baseEnd_1904952 : Nat := 978155999743736100239291

theorem tailTrace_1904952 : CollatzResearch.WordTrace tailWord_1904952 prefixEnd_1904952 978155999743736100239291 := by
  unfold tailWord_1904952
  simp only [CollatzResearch.WordTrace]
  refine ⟨34739653697345859372538555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46319538263127812496718073 34739653697345859372538555)
  ·
    refine ⟨52109480546018789058807833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34739653697345859372538555 52109480546018789058807833)
    ·
      refine ⟨39082110409514091794105875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52109480546018789058807833 39082110409514091794105875)
      ·
        refine ⟨58623165614271137691158813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39082110409514091794105875 58623165614271137691158813)
        ·
          refine ⟨21983687105351676634184555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58623165614271137691158813 21983687105351676634184555)
          ·
            refine ⟨32975530658027514951276833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21983687105351676634184555 32975530658027514951276833)
            ·
              refine ⟨24731647993520636213457625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32975530658027514951276833 24731647993520636213457625)
              ·
                refine ⟨18548735995140477160093219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24731647993520636213457625 18548735995140477160093219)
                ·
                  refine ⟨27823103992710715740139829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18548735995140477160093219 27823103992710715740139829)
                  ·
                    refine ⟨2608415999316629600638109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27823103992710715740139829 2608415999316629600638109)
                    ·
                      refine ⟨978155999743736100239291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2608415999316629600638109 978155999743736100239291)
                      ·
                        rfl

theorem cell23_1904952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_1904952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904952 prefixEnd_1904952 := by exact prefixLift 1904952
  have htrace : WordTrace (prefixWord ++ tailWord_1904952) baseStart_1904952 baseEnd_1904952 := by
    simpa [prefixWord, tailWord_1904952, baseEnd_1904952] using wordTrace_append hprefix tailTrace_1904952
  have hstable : (prefixWord ++ tailWord_1904952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904952).length < 2 ^ (prefixWord ++ tailWord_1904952).sum := by decide
  have hdescent : baseEnd_1904952 < baseStart_1904952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904976 : List Nat := [2, 1, 1, 1, 1, 7, 3, 2, 5]
def baseStart_1904976 : Nat := 118140960795 + 1904976 * 2 ^ 59
def prefixEnd_1904976 : Nat := 4983230072969 + 3 ^ 40 * 1904976 * 2
def baseEnd_1904976 : Nat := 108685369253271556259909

theorem tailTrace_1904976 : CollatzResearch.WordTrace tailWord_1904976 prefixEnd_1904976 108685369253271556259909 := by
  unfold tailWord_1904976
  simp only [CollatzResearch.WordTrace]
  refine ⟨34740091373302385421975391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46320121831069847229300521 34740091373302385421975391)
  ·
    refine ⟨52110137059953578132963087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34740091373302385421975391 52110137059953578132963087)
    ·
      refine ⟨78165205589930367199444631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52110137059953578132963087 78165205589930367199444631)
      ·
        refine ⟨117247808384895550799166947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78165205589930367199444631 117247808384895550799166947)
        ·
          refine ⟨175871712577343326198750421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117247808384895550799166947 175871712577343326198750421)
          ·
            refine ⟨4121993263531484207783213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175871712577343326198750421 4121993263531484207783213)
            ·
              refine ⟨1545747473824306577918705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4121993263531484207783213 1545747473824306577918705)
              ·
                refine ⟨1159310605368229933439029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545747473824306577918705 1159310605368229933439029)
                ·
                  refine ⟨108685369253271556259909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1159310605368229933439029 108685369253271556259909)
                  ·
                    rfl

theorem cell23_1904976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 5].length) (baseStart_1904976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1904976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1904976 prefixEnd_1904976 := by exact prefixLift 1904976
  have htrace : WordTrace (prefixWord ++ tailWord_1904976) baseStart_1904976 baseEnd_1904976 := by
    simpa [prefixWord, tailWord_1904976, baseEnd_1904976] using wordTrace_append hprefix tailTrace_1904976
  have hstable : (prefixWord ++ tailWord_1904976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904976).length < 2 ^ (prefixWord ++ tailWord_1904976).sum := by decide
  have hdescent : baseEnd_1904976 < baseStart_1904976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905009 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 4, 4, 2]
def baseStart_1905009 : Nat := 118140960795 + 1905009 * 2 ^ 59
def prefixEnd_1905009 : Nat := 4983230072969 + 3 ^ 40 * 1905009 * 2
def baseEnd_1905009 : Nat := 978185268141042377226529

theorem tailTrace_1905009 : CollatzResearch.WordTrace tailWord_1905009 prefixEnd_1905009 978185268141042377226529 := by
  unfold tailWord_1905009
  simp only [CollatzResearch.WordTrace]
  refine ⟨69481386355485217479902081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46320924236990144986601387 69481386355485217479902081)
  ·
    refine ⟨52111039766613913109926561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69481386355485217479902081 52111039766613913109926561)
    ·
      refine ⟨39083279824960434832444921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52111039766613913109926561 39083279824960434832444921)
      ·
        refine ⟨29312459868720326124333691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39083279824960434832444921 29312459868720326124333691)
        ·
          refine ⟨43968689803080489186500537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29312459868720326124333691 43968689803080489186500537)
          ·
            refine ⟨32976517352310366889875403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43968689803080489186500537 32976517352310366889875403)
            ·
              refine ⟨49464776028465550334813105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32976517352310366889875403 49464776028465550334813105)
              ·
                refine ⟨37098582021349162751109829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49464776028465550334813105 37098582021349162751109829)
                ·
                  refine ⟨6955984129002968015833093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37098582021349162751109829 6955984129002968015833093)
                  ·
                    refine ⟨1304247024188056502968705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6955984129002968015833093 1304247024188056502968705)
                    ·
                      refine ⟨978185268141042377226529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304247024188056502968705 978185268141042377226529)
                      ·
                        rfl

theorem cell23_1905009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_1905009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905009 prefixEnd_1905009 := by exact prefixLift 1905009
  have htrace : WordTrace (prefixWord ++ tailWord_1905009) baseStart_1905009 baseEnd_1905009 := by
    simpa [prefixWord, tailWord_1905009, baseEnd_1905009] using wordTrace_append hprefix tailTrace_1905009
  have hstable : (prefixWord ++ tailWord_1905009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905009).length < 2 ^ (prefixWord ++ tailWord_1905009).sum := by decide
  have hdescent : baseEnd_1905009 < baseStart_1905009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905063 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1905063 : Nat := 118140960795 + 1905063 * 2 ^ 59
def prefixEnd_1905063 : Nat := 4983230072969 + 3 ^ 40 * 1905063 * 2
def baseEnd_1905063 : Nat := 978212996096385165951281

theorem tailTrace_1905063 : CollatzResearch.WordTrace tailWord_1905063 prefixEnd_1905063 978212996096385165951281 := by
  unfold tailWord_1905063
  simp only [CollatzResearch.WordTrace]
  refine ⟨69483355897289584702367843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46322237264859723134911895 69483355897289584702367843)
  ·
    refine ⟨104225033845934377053551765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69483355897289584702367843 104225033845934377053551765)
    ·
      refine ⟨4885548461528173924385239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104225033845934377053551765 4885548461528173924385239)
      ·
        refine ⟨7328322692292260886577859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885548461528173924385239 7328322692292260886577859)
        ·
          refine ⟨10992484038438391329866789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328322692292260886577859 10992484038438391329866789)
          ·
            refine ⟨2061090757207198374350023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10992484038438391329866789 2061090757207198374350023)
            ·
              refine ⟨3091636135810797561525035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061090757207198374350023 3091636135810797561525035)
              ·
                refine ⟨4637454203716196342287553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091636135810797561525035 4637454203716196342287553)
                ·
                  refine ⟨3478090652787147256715665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4637454203716196342287553 3478090652787147256715665)
                  ·
                    refine ⟨2608567989590360442536749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3478090652787147256715665 2608567989590360442536749)
                    ·
                      refine ⟨978212996096385165951281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2608567989590360442536749 978212996096385165951281)
                      ·
                        rfl

theorem cell23_1905063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1905063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905063 prefixEnd_1905063 := by exact prefixLift 1905063
  have htrace : WordTrace (prefixWord ++ tailWord_1905063) baseStart_1905063 baseEnd_1905063 := by
    simpa [prefixWord, tailWord_1905063, baseEnd_1905063] using wordTrace_append hprefix tailTrace_1905063
  have hstable : (prefixWord ++ tailWord_1905063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905063).length < 2 ^ (prefixWord ++ tailWord_1905063).sum := by decide
  have hdescent : baseEnd_1905063 < baseStart_1905063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905133 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1905133 : Nat := 118140960795 + 1905133 * 2 ^ 59
def prefixEnd_1905133 : Nat := 4983230072969 + 3 ^ 40 * 1905133 * 2
def baseEnd_1905133 : Nat := 978248939742199892075959

theorem tailTrace_1905133 : CollatzResearch.WordTrace tailWord_1905133 prefixEnd_1905133 978248939742199892075959 := by
  unfold tailWord_1905133
  simp only [CollatzResearch.WordTrace]
  refine ⟨69485909007035986657416053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46323939338023991104944035 69485909007035986657416053)
  ·
    refine ⟨6514303969409623749132755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69485909007035986657416053 6514303969409623749132755)
    ·
      refine ⟨9771455954114435623699133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6514303969409623749132755 9771455954114435623699133)
      ·
        refine ⟨3664295982792913358887175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9771455954114435623699133 3664295982792913358887175)
        ·
          refine ⟨5496443974189370038330763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664295982792913358887175 5496443974189370038330763)
          ·
            refine ⟨8244665961284055057496145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5496443974189370038330763 8244665961284055057496145)
            ·
              refine ⟨6183499470963041293122109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8244665961284055057496145 6183499470963041293122109)
              ·
                refine ⟨2318812301611140484920791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6183499470963041293122109 2318812301611140484920791)
                ·
                  refine ⟨3478218452416710727381187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318812301611140484920791 3478218452416710727381187)
                  ·
                    refine ⟨5217327678625066091071781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3478218452416710727381187 5217327678625066091071781)
                    ·
                      refine ⟨978248939742199892075959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5217327678625066091071781 978248939742199892075959)
                      ·
                        rfl

theorem cell23_1905133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1905133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905133 prefixEnd_1905133 := by exact prefixLift 1905133
  have htrace : WordTrace (prefixWord ++ tailWord_1905133) baseStart_1905133 baseEnd_1905133 := by
    simpa [prefixWord, tailWord_1905133, baseEnd_1905133] using wordTrace_append hprefix tailTrace_1905133
  have hstable : (prefixWord ++ tailWord_1905133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905133).length < 2 ^ (prefixWord ++ tailWord_1905133).sum := by decide
  have hdescent : baseEnd_1905133 < baseStart_1905133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905136 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3]
def baseStart_1905136 : Nat := 118140960795 + 1905136 * 2 ^ 59
def prefixEnd_1905136 : Nat := 4983230072969 + 3 ^ 40 * 1905136 * 2
def baseEnd_1905136 : Nat := 978250480184163380338445

theorem tailTrace_1905136 : CollatzResearch.WordTrace tailWord_1905136 prefixEnd_1905136 978250480184163380338445 := by
  unfold tailWord_1905136
  simp only [CollatzResearch.WordTrace]
  refine ⟨34743009213012559084887631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46324012284016745446516841 34743009213012559084887631)
  ·
    refine ⟨52114513819518838627331447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34743009213012559084887631 52114513819518838627331447)
    ·
      refine ⟨78171770729278257940997171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52114513819518838627331447 78171770729278257940997171)
      ·
        refine ⟨117257656093917386911495757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78171770729278257940997171 117257656093917386911495757)
        ·
          refine ⟨43971621035219020091810909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117257656093917386911495757 43971621035219020091810909)
          ·
            refine ⟨16489357888207132534429091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43971621035219020091810909 16489357888207132534429091)
            ·
              refine ⟨24734036832310698801643637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16489357888207132534429091 24734036832310698801643637)
              ·
                refine ⟨2318815953029128012654091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24734036832310698801643637 2318815953029128012654091)
                ·
                  refine ⟨3478223929543692018981137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318815953029128012654091 3478223929543692018981137)
                  ·
                    refine ⟨2608667947157769014235853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3478223929543692018981137 2608667947157769014235853)
                    ·
                      refine ⟨978250480184163380338445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2608667947157769014235853 978250480184163380338445)
                      ·
                        rfl

theorem cell23_1905136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_1905136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905136 prefixEnd_1905136 := by exact prefixLift 1905136
  have htrace : WordTrace (prefixWord ++ tailWord_1905136) baseStart_1905136 baseEnd_1905136 := by
    simpa [prefixWord, tailWord_1905136, baseEnd_1905136] using wordTrace_append hprefix tailTrace_1905136
  have hstable : (prefixWord ++ tailWord_1905136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905136).length < 2 ^ (prefixWord ++ tailWord_1905136).sum := by decide
  have hdescent : baseEnd_1905136 < baseStart_1905136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905156 : List Nat := [2, 3, 2, 3, 1, 2, 2, 8]
def baseStart_1905156 : Nat := 118140960795 + 1905156 * 2 ^ 59
def prefixEnd_1905156 : Nat := 4983230072969 + 3 ^ 40 * 1905156 * 2
def baseEnd_1905156 : Nat := 36231879622120492669939

theorem tailTrace_1905156 : CollatzResearch.WordTrace tailWord_1905156 prefixEnd_1905156 36231879622120492669939 := by
  unfold tailWord_1905156
  simp only [CollatzResearch.WordTrace]
  refine ⟨34743373942976330792751661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46324498590635107723668881 34743373942976330792751661)
  ·
    refine ⟨13028765228616124047281873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34743373942976330792751661 13028765228616124047281873)
    ·
      refine ⟨9771573921462093035461405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13028765228616124047281873 9771573921462093035461405)
      ·
        refine ⟨3664340220548284888298027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9771573921462093035461405 3664340220548284888298027)
        ·
          refine ⟨5496510330822427332447041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664340220548284888298027 5496510330822427332447041)
          ·
            refine ⟨4122382748116820499335281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5496510330822427332447041 4122382748116820499335281)
            ·
              refine ⟨3091787061087615374501461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122382748116820499335281 3091787061087615374501461)
              ·
                refine ⟨36231879622120492669939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3091787061087615374501461 36231879622120492669939)
                ·
                  rfl

theorem cell23_1905156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 8].length) (baseStart_1905156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905156 prefixEnd_1905156 := by exact prefixLift 1905156
  have htrace : WordTrace (prefixWord ++ tailWord_1905156) baseStart_1905156 baseEnd_1905156 := by
    simpa [prefixWord, tailWord_1905156, baseEnd_1905156] using wordTrace_append hprefix tailTrace_1905156
  have hstable : (prefixWord ++ tailWord_1905156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905156).length < 2 ^ (prefixWord ++ tailWord_1905156).sum := by decide
  have hdescent : baseEnd_1905156 < baseStart_1905156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905223 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_1905223 : Nat := 118140960795 + 1905223 * 2 ^ 59
def prefixEnd_1905223 : Nat := 4983230072969 + 3 ^ 40 * 1905223 * 2
def baseEnd_1905223 : Nat := 978295153001104539950545

theorem tailTrace_1905223 : CollatzResearch.WordTrace tailWord_1905223 prefixEnd_1905223 978295153001104539950545 := by
  unfold tailWord_1905223
  simp only [CollatzResearch.WordTrace]
  refine ⟨69489191576709932028192323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46326127717806621352128215 69489191576709932028192323)
  ·
    refine ⟨104233787365064898042288485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69489191576709932028192323 104233787365064898042288485)
    ·
      refine ⟨19543835130949668382929091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104233787365064898042288485 19543835130949668382929091)
      ·
        refine ⟨29315752696424502574393637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19543835130949668382929091 29315752696424502574393637)
        ·
          refine ⟨5496703630579594232698807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29315752696424502574393637 5496703630579594232698807)
          ·
            refine ⟨8245055445869391349048211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5496703630579594232698807 8245055445869391349048211)
            ·
              refine ⟨12367583168804087023572317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245055445869391349048211 12367583168804087023572317)
              ·
                refine ⟨4637843688301532633839619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12367583168804087023572317 4637843688301532633839619)
                ·
                  refine ⟨6956765532452298950759429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637843688301532633839619 6956765532452298950759429)
                  ·
                    refine ⟨1304393537334806053267393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956765532452298950759429 1304393537334806053267393)
                    ·
                      refine ⟨978295153001104539950545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304393537334806053267393 978295153001104539950545)
                      ·
                        rfl

theorem cell23_1905223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_1905223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905223 prefixEnd_1905223 := by exact prefixLift 1905223
  have htrace : WordTrace (prefixWord ++ tailWord_1905223) baseStart_1905223 baseEnd_1905223 := by
    simpa [prefixWord, tailWord_1905223, baseEnd_1905223] using wordTrace_append hprefix tailTrace_1905223
  have hstable : (prefixWord ++ tailWord_1905223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905223).length < 2 ^ (prefixWord ++ tailWord_1905223).sum := by decide
  have hdescent : baseEnd_1905223 < baseStart_1905223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905244 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_1905244 : Nat := 118140960795 + 1905244 * 2 ^ 59
def prefixEnd_1905244 : Nat := 4983230072969 + 3 ^ 40 * 1905244 * 2
def baseEnd_1905244 : Nat := 978305936094848957787949

theorem tailTrace_1905244 : CollatzResearch.WordTrace tailWord_1905244 prefixEnd_1905244 978305936094848957787949 := by
  unfold tailWord_1905244
  simp only [CollatzResearch.WordTrace]
  refine ⟨34744978754816926307353393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46326638339755901743137857 34744978754816926307353393)
  ·
    refine ⟨26058734066112694730515045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34744978754816926307353393 26058734066112694730515045)
    ·
      refine ⟨4886012637396130261971571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26058734066112694730515045 4886012637396130261971571)
      ·
        refine ⟨7329018956094195392957357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886012637396130261971571 7329018956094195392957357)
        ·
          refine ⟨2748382108535323272359009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7329018956094195392957357 2748382108535323272359009)
          ·
            refine ⟨2061286581401492454269257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748382108535323272359009 2061286581401492454269257)
            ·
              refine ⟨1545964936051119340701943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061286581401492454269257 1545964936051119340701943)
              ·
                refine ⟨2318947404076679011052915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545964936051119340701943 2318947404076679011052915)
                ·
                  refine ⟨3478421106115018516579373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318947404076679011052915 3478421106115018516579373)
                  ·
                    refine ⟨1304407914793131943717265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3478421106115018516579373 1304407914793131943717265)
                    ·
                      refine ⟨978305936094848957787949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304407914793131943717265 978305936094848957787949)
                      ·
                        rfl

theorem cell23_1905244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_1905244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905244 prefixEnd_1905244 := by exact prefixLift 1905244
  have htrace : WordTrace (prefixWord ++ tailWord_1905244) baseStart_1905244 baseEnd_1905244 := by
    simpa [prefixWord, tailWord_1905244, baseEnd_1905244] using wordTrace_append hprefix tailTrace_1905244
  have hstable : (prefixWord ++ tailWord_1905244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905244).length < 2 ^ (prefixWord ++ tailWord_1905244).sum := by decide
  have hdescent : baseEnd_1905244 < baseStart_1905244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905289 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 10]
def baseStart_1905289 : Nat := 118140960795 + 1905289 * 2 ^ 59
def prefixEnd_1905289 : Nat := 4983230072969 + 3 ^ 40 * 1905289 * 2
def baseEnd_1905289 : Nat := 326109680908100427241747

theorem tailTrace_1905289 : CollatzResearch.WordTrace tailWord_1905289 prefixEnd_1905289 326109680908100427241747 := by
  unfold tailWord_1905289
  simp only [CollatzResearch.WordTrace]
  refine ⟨69491598794470825300094921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46327732529647216866729947 69491598794470825300094921)
  ·
    refine ⟨52118699095853118975071191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69491598794470825300094921 52118699095853118975071191)
    ·
      refine ⟨78178048643779678462606787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52118699095853118975071191 78178048643779678462606787)
      ·
        refine ⟨117267072965669517693910181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78178048643779678462606787 117267072965669517693910181)
        ·
          refine ⟨21987576181063034567608159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117267072965669517693910181 21987576181063034567608159)
          ·
            refine ⟨32981364271594551851412239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21987576181063034567608159 32981364271594551851412239)
            ·
              refine ⟨49472046407391827777118359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32981364271594551851412239 49472046407391827777118359)
              ·
                refine ⟨74208069611087741665677539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49472046407391827777118359 74208069611087741665677539)
                ·
                  refine ⟨111312104416631612498516309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74208069611087741665677539 111312104416631612498516309)
                  ·
                    refine ⟨326109680908100427241747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 111312104416631612498516309 326109680908100427241747)
                    ·
                      rfl

theorem cell23_1905289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_1905289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905289 prefixEnd_1905289 := by exact prefixLift 1905289
  have htrace : WordTrace (prefixWord ++ tailWord_1905289) baseStart_1905289 baseEnd_1905289 := by
    simpa [prefixWord, tailWord_1905289, baseEnd_1905289] using wordTrace_append hprefix tailTrace_1905289
  have hstable : (prefixWord ++ tailWord_1905289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905289).length < 2 ^ (prefixWord ++ tailWord_1905289).sum := by decide
  have hdescent : baseEnd_1905289 < baseStart_1905289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905420 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 7, 2, 2]
def baseStart_1905420 : Nat := 118140960795 + 1905420 * 2 ^ 59
def prefixEnd_1905420 : Nat := 4983230072969 + 3 ^ 40 * 1905420 * 2
def baseEnd_1905420 : Nat := 978396308690040269187139

theorem tailTrace_1905420 : CollatzResearch.WordTrace tailWord_1905420 prefixEnd_1905420 978396308690040269187139 := by
  unfold tailWord_1905420
  simp only [CollatzResearch.WordTrace]
  refine ⟨34748188378498117336556857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46330917837997489782075809 34748188378498117336556857)
  ·
    refine ⟨26061141283873588002417643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34748188378498117336556857 26061141283873588002417643)
    ·
      refine ⟨39091711925810382003626465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26061141283873588002417643 39091711925810382003626465)
      ·
        refine ⟨29318783944357786502719849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39091711925810382003626465 29318783944357786502719849)
        ·
          refine ⟨21989087958268339877039887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29318783944357786502719849 21989087958268339877039887)
          ·
            refine ⟨32983631937402509815559831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21989087958268339877039887 32983631937402509815559831)
            ·
              refine ⟨49475447906103764723339747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32983631937402509815559831 49475447906103764723339747)
              ·
                refine ⟨74213171859155647085009621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49475447906103764723339747 74213171859155647085009621)
                ·
                  refine ⟨1739371215448960478554913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74213171859155647085009621 1739371215448960478554913)
                  ·
                    refine ⟨1304528411586720358916185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1739371215448960478554913 1304528411586720358916185)
                    ·
                      refine ⟨978396308690040269187139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304528411586720358916185 978396308690040269187139)
                      ·
                        rfl

theorem cell23_1905420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_1905420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905420 prefixEnd_1905420 := by exact prefixLift 1905420
  have htrace : WordTrace (prefixWord ++ tailWord_1905420) baseStart_1905420 baseEnd_1905420 := by
    simpa [prefixWord, tailWord_1905420, baseEnd_1905420] using wordTrace_append hprefix tailTrace_1905420
  have hstable : (prefixWord ++ tailWord_1905420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905420).length < 2 ^ (prefixWord ++ tailWord_1905420).sum := by decide
  have hdescent : baseEnd_1905420 < baseStart_1905420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905454 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1905454 : Nat := 118140960795 + 1905454 * 2 ^ 59
def prefixEnd_1905454 : Nat := 4983230072969 + 3 ^ 40 * 1905454 * 2
def baseEnd_1905454 : Nat := 978413767032293136161983

theorem tailTrace_1905454 : CollatzResearch.WordTrace tailWord_1905454 prefixEnd_1905454 978413767032293136161983 := by
  unfold tailWord_1905454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687202104859132309981427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46331744559248705653234277 8687202104859132309981427)
  ·
    refine ⟨13030803157288698464972141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8687202104859132309981427 13030803157288698464972141)
    ·
      refine ⟨4886551183983261924364553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13030803157288698464972141 4886551183983261924364553)
      ·
        refine ⟨3664913387987446443273415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4886551183983261924364553 3664913387987446443273415)
        ·
          refine ⟨5497370081981169664910123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664913387987446443273415 5497370081981169664910123)
          ·
            refine ⟨8246055122971754497365185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497370081981169664910123 8246055122971754497365185)
            ·
              refine ⟨6184541342228815873023889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8246055122971754497365185 6184541342228815873023889)
              ·
                refine ⟨4638406006671611904767917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6184541342228815873023889 4638406006671611904767917)
                ·
                  refine ⟨1739402252501854464287969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4638406006671611904767917 1739402252501854464287969)
                  ·
                    refine ⟨1304551689376390848215977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1739402252501854464287969 1304551689376390848215977)
                    ·
                      refine ⟨978413767032293136161983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304551689376390848215977 978413767032293136161983)
                      ·
                        rfl

theorem cell23_1905454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1905454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905454 prefixEnd_1905454 := by exact prefixLift 1905454
  have htrace : WordTrace (prefixWord ++ tailWord_1905454) baseStart_1905454 baseEnd_1905454 := by
    simpa [prefixWord, tailWord_1905454, baseEnd_1905454] using wordTrace_append hprefix tailTrace_1905454
  have hstable : (prefixWord ++ tailWord_1905454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905454).length < 2 ^ (prefixWord ++ tailWord_1905454).sum := by decide
  have hdescent : baseEnd_1905454 < baseStart_1905454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905456 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 2, 7]
def baseStart_1905456 : Nat := 118140960795 + 1905456 * 2 ^ 59
def prefixEnd_1905456 : Nat := 4983230072969 + 3 ^ 40 * 1905456 * 2
def baseEnd_1905456 : Nat := 326138264664534042778991

theorem tailTrace_1905456 : CollatzResearch.WordTrace tailWord_1905456 prefixEnd_1905456 326138264664534042778991 := by
  unfold tailWord_1905456
  simp only [CollatzResearch.WordTrace]
  refine ⟨34748844892432906410712111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46331793189910541880949481 34748844892432906410712111)
  ·
    refine ⟨52123267338649359616068167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34748844892432906410712111 52123267338649359616068167)
    ·
      refine ⟨78184901007974039424102251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52123267338649359616068167 78184901007974039424102251)
      ·
        refine ⟨117277351511961059136153377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78184901007974039424102251 117277351511961059136153377)
        ·
          refine ⟨87958013633970794352115033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117277351511961059136153377 87958013633970794352115033)
          ·
            refine ⟨65968510225478095764086275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87958013633970794352115033 65968510225478095764086275)
            ·
              refine ⟨98952765338217143646129413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65968510225478095764086275 98952765338217143646129413)
              ·
                refine ⟨18553643500915714433649265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98952765338217143646129413 18553643500915714433649265)
                ·
                  refine ⟨13915232625686785825236949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18553643500915714433649265 13915232625686785825236949)
                  ·
                    refine ⟨326138264664534042778991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13915232625686785825236949 326138264664534042778991)
                    ·
                      rfl

theorem cell23_1905456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_1905456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905456 prefixEnd_1905456 := by exact prefixLift 1905456
  have htrace : WordTrace (prefixWord ++ tailWord_1905456) baseStart_1905456 baseEnd_1905456 := by
    simpa [prefixWord, tailWord_1905456, baseEnd_1905456] using wordTrace_append hprefix tailTrace_1905456
  have hstable : (prefixWord ++ tailWord_1905456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905456).length < 2 ^ (prefixWord ++ tailWord_1905456).sum := by decide
  have hdescent : baseEnd_1905456 < baseStart_1905456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905460 : List Nat := [2, 5, 1, 1, 3, 1, 1, 9]
def baseStart_1905460 : Nat := 118140960795 + 1905460 * 2 ^ 59
def prefixEnd_1905460 : Nat := 4983230072969 + 3 ^ 40 * 1905460 * 2
def baseEnd_1905460 : Nat := 36237661033934078247665

theorem tailTrace_1905460 : CollatzResearch.WordTrace tailWord_1905460 prefixEnd_1905460 36237661033934078247665 := by
  unfold tailWord_1905460
  simp only [CollatzResearch.WordTrace]
  refine ⟨34748917838425660752284917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46331890451234214336379889 34748917838425660752284917)
  ·
    refine ⟨3257711047352405695526711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34748917838425660752284917 3257711047352405695526711)
    ·
      refine ⟨4886566571028608543290067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257711047352405695526711 4886566571028608543290067)
      ·
        refine ⟨7329849856542912814935101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886566571028608543290067 7329849856542912814935101)
        ·
          refine ⟨2748693696203592305600663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7329849856542912814935101 2748693696203592305600663)
          ·
            refine ⟨4123040544305388458400995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748693696203592305600663 4123040544305388458400995)
            ·
              refine ⟨6184560816458082687601493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123040544305388458400995 6184560816458082687601493)
              ·
                refine ⟨36237661033934078247665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6184560816458082687601493 36237661033934078247665)
                ·
                  rfl

theorem cell23_1905460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 9].length) (baseStart_1905460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905460 prefixEnd_1905460 := by exact prefixLift 1905460
  have htrace : WordTrace (prefixWord ++ tailWord_1905460) baseStart_1905460 baseEnd_1905460 := by
    simpa [prefixWord, tailWord_1905460, baseEnd_1905460] using wordTrace_append hprefix tailTrace_1905460
  have hstable : (prefixWord ++ tailWord_1905460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905460).length < 2 ^ (prefixWord ++ tailWord_1905460).sum := by decide
  have hdescent : baseEnd_1905460 < baseStart_1905460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905471 : List Nat := [1, 1, 2, 2, 5, 3, 1, 3, 1, 2, 2]
def baseStart_1905471 : Nat := 118140960795 + 1905471 * 2 ^ 59
def prefixEnd_1905471 : Nat := 4983230072969 + 3 ^ 40 * 1905471 * 2
def baseEnd_1905471 : Nat := 978422496203419569649405

theorem tailTrace_1905471 : CollatzResearch.WordTrace tailWord_1905471 prefixEnd_1905471 978422496203419569649405 := by
  unfold tailWord_1905471
  simp only [CollatzResearch.WordTrace]
  refine ⟨69498236879811470383220267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46332157919874313588813511 69498236879811470383220267)
  ·
    refine ⟨104247355319717205574830401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69498236879811470383220267 104247355319717205574830401)
    ·
      refine ⟨78185516489787904181122801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104247355319717205574830401 78185516489787904181122801)
      ·
        refine ⟨58639137367340928135842101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78185516489787904181122801 58639137367340928135842101)
        ·
          refine ⟨5497419128188212012735197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58639137367340928135842101 5497419128188212012735197)
          ·
            refine ⟨2061532173070579504775699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5497419128188212012735197 2061532173070579504775699)
            ·
              refine ⟨3092298259605869257163549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061532173070579504775699 3092298259605869257163549)
              ·
                refine ⟨1159611847352200971436331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3092298259605869257163549 1159611847352200971436331)
                ·
                  refine ⟨1739417771028301457154497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159611847352200971436331 1739417771028301457154497)
                  ·
                    refine ⟨1304563328271226092865873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1739417771028301457154497 1304563328271226092865873)
                    ·
                      refine ⟨978422496203419569649405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304563328271226092865873 978422496203419569649405)
                      ·
                        rfl

theorem cell23_1905471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_1905471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905471 prefixEnd_1905471 := by exact prefixLift 1905471
  have htrace : WordTrace (prefixWord ++ tailWord_1905471) baseStart_1905471 baseEnd_1905471 := by
    simpa [prefixWord, tailWord_1905471, baseEnd_1905471] using wordTrace_append hprefix tailTrace_1905471
  have hstable : (prefixWord ++ tailWord_1905471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905471).length < 2 ^ (prefixWord ++ tailWord_1905471).sum := by decide
  have hdescent : baseEnd_1905471 < baseStart_1905471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905493 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1905493 : Nat := 118140960795 + 1905493 * 2 ^ 59
def prefixEnd_1905493 : Nat := 4983230072969 + 3 ^ 40 * 1905493 * 2
def baseEnd_1905493 : Nat := 978433792777818483574303

theorem tailTrace_1905493 : CollatzResearch.WordTrace tailWord_1905493 prefixEnd_1905493 978433792777818483574303 := by
  unfold tailWord_1905493
  simp only [CollatzResearch.WordTrace]
  refine ⟨69499039285731768140521133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46332692857154512093680755 69499039285731768140521133)
  ·
    refine ⟨26062139732149413052695425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69499039285731768140521133 26062139732149413052695425)
    ·
      refine ⟨19546604799112059789521569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26062139732149413052695425 19546604799112059789521569)
      ·
        refine ⟨14659953599334044842141177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19546604799112059789521569 14659953599334044842141177)
        ·
          refine ⟨10994965199500533631605883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14659953599334044842141177 10994965199500533631605883)
          ·
            refine ⟨16492447799250800447408825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10994965199500533631605883 16492447799250800447408825)
            ·
              refine ⟨12369335849438100335556619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16492447799250800447408825 12369335849438100335556619)
              ·
                refine ⟨18554003774157150503334929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12369335849438100335556619 18554003774157150503334929)
                ·
                  refine ⟨13915502830617862877501197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18554003774157150503334929 13915502830617862877501197)
                  ·
                    refine ⟨5218313561481698579062949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13915502830617862877501197 5218313561481698579062949)
                    ·
                      refine ⟨978433792777818483574303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5218313561481698579062949 978433792777818483574303)
                      ·
                        rfl

theorem cell23_1905493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1905493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905493 prefixEnd_1905493 := by exact prefixLift 1905493
  have htrace : WordTrace (prefixWord ++ tailWord_1905493) baseStart_1905493 baseEnd_1905493 := by
    simpa [prefixWord, tailWord_1905493, baseEnd_1905493] using wordTrace_append hprefix tailTrace_1905493
  have hstable : (prefixWord ++ tailWord_1905493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905493).length < 2 ^ (prefixWord ++ tailWord_1905493).sum := by decide
  have hdescent : baseEnd_1905493 < baseStart_1905493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905538 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1905538 : Nat := 118140960795 + 1905538 * 2 ^ 59
def prefixEnd_1905538 : Nat := 4983230072969 + 3 ^ 40 * 1905538 * 2
def baseEnd_1905538 : Nat := 978456899407270807511597

theorem tailTrace_1905538 : CollatzResearch.WordTrace tailWord_1905538 prefixEnd_1905538 978456899407270807511597 := by
  unfold tailWord_1905538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17375170142642185206477317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46333787047045827217272845 17375170142642185206477317)
  ·
    refine ⟨3257844401745409726214497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17375170142642185206477317 3257844401745409726214497)
    ·
      refine ⟨2443383301309057294660873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3257844401745409726214497 2443383301309057294660873)
      ·
        refine ⟨1832537475981792970995655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2443383301309057294660873 1832537475981792970995655)
        ·
          refine ⟨2748806213972689456493483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832537475981792970995655 2748806213972689456493483)
          ·
            refine ⟨4123209320959034184740225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748806213972689456493483 4123209320959034184740225)
            ·
              refine ⟨3092406990719275638555169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123209320959034184740225 3092406990719275638555169)
              ·
                refine ⟨2319305243039456728916377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092406990719275638555169 2319305243039456728916377)
                ·
                  refine ⟨1739478932279592546687283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2319305243039456728916377 1739478932279592546687283)
                  ·
                    refine ⟨2609218398419388820030925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1739478932279592546687283 2609218398419388820030925)
                    ·
                      refine ⟨978456899407270807511597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2609218398419388820030925 978456899407270807511597)
                      ·
                        rfl

theorem cell23_1905538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1905538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905538 prefixEnd_1905538 := by exact prefixLift 1905538
  have htrace : WordTrace (prefixWord ++ tailWord_1905538) baseStart_1905538 baseEnd_1905538 := by
    simpa [prefixWord, tailWord_1905538, baseEnd_1905538] using wordTrace_append hprefix tailTrace_1905538
  have hstable : (prefixWord ++ tailWord_1905538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905538).length < 2 ^ (prefixWord ++ tailWord_1905538).sum := by decide
  have hdescent : baseEnd_1905538 < baseStart_1905538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905544 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1905544 : Nat := 118140960795 + 1905544 * 2 ^ 59
def prefixEnd_1905544 : Nat := 4983230072969 + 3 ^ 40 * 1905544 * 2
def baseEnd_1905544 : Nat := 978459980291197784036569

theorem tailTrace_1905544 : CollatzResearch.WordTrace tailWord_1905544 prefixEnd_1905544 978459980291197784036569 := by
  unfold tailWord_1905544
  simp only [CollatzResearch.WordTrace]
  refine ⟨34750449704273501925313843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46333932939031335900418457 34750449704273501925313843)
  ·
    refine ⟨52125674556410252887970765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34750449704273501925313843 52125674556410252887970765)
    ·
      refine ⟨19547127958653844832989037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52125674556410252887970765 19547127958653844832989037)
      ·
        refine ⟨7330172984495191812370889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19547127958653844832989037 7330172984495191812370889)
        ·
          refine ⟨5497629738371393859278167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7330172984495191812370889 5497629738371393859278167)
          ·
            refine ⟨8246444607557090788917251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497629738371393859278167 8246444607557090788917251)
            ·
              refine ⟨12369666911335636183375877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246444607557090788917251 12369666911335636183375877)
              ·
                refine ⟨2319312545875431784382977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12369666911335636183375877 2319312545875431784382977)
                ·
                  refine ⟨1739484409406573838287233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2319312545875431784382977 1739484409406573838287233)
                  ·
                    refine ⟨1304613307054930378715425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1739484409406573838287233 1304613307054930378715425)
                    ·
                      refine ⟨978459980291197784036569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304613307054930378715425 978459980291197784036569)
                      ·
                        rfl

theorem cell23_1905544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1905544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905544 prefixEnd_1905544 := by exact prefixLift 1905544
  have htrace : WordTrace (prefixWord ++ tailWord_1905544) baseStart_1905544 baseEnd_1905544 := by
    simpa [prefixWord, tailWord_1905544, baseEnd_1905544] using wordTrace_append hprefix tailTrace_1905544
  have hstable : (prefixWord ++ tailWord_1905544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905544).length < 2 ^ (prefixWord ++ tailWord_1905544).sum := by decide
  have hdescent : baseEnd_1905544 < baseStart_1905544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905654 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1905654 : Nat := 118140960795 + 1905654 * 2 ^ 59
def prefixEnd_1905654 : Nat := 4983230072969 + 3 ^ 40 * 1905654 * 2
def baseEnd_1905654 : Nat := 978516463163192353661063

theorem tailTrace_1905654 : CollatzResearch.WordTrace tailWord_1905654 prefixEnd_1905654 978516463163192353661063 := by
  unfold tailWord_1905654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344056964884280789820751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46336607625432328424754677 4344056964884280789820751)
  ·
    refine ⟨6516085447326421184731127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4344056964884280789820751 6516085447326421184731127)
    ·
      refine ⟨9774128170989631777096691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516085447326421184731127 9774128170989631777096691)
      ·
        refine ⟨14661192256484447665645037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9774128170989631777096691 14661192256484447665645037)
        ·
          refine ⟨5497947096181667874616889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14661192256484447665645037 5497947096181667874616889)
          ·
            refine ⟨4123460322136250905962667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5497947096181667874616889 4123460322136250905962667)
            ·
              refine ⟨6185190483204376358944001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123460322136250905962667 6185190483204376358944001)
              ·
                refine ⟨4638892862403282269208001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6185190483204376358944001 4638892862403282269208001)
                ·
                  refine ⟨3479169646802461701906001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638892862403282269208001 3479169646802461701906001)
                  ·
                    refine ⟨2609377235101846276429501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3479169646802461701906001 2609377235101846276429501)
                    ·
                      refine ⟨978516463163192353661063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2609377235101846276429501 978516463163192353661063)
                      ·
                        rfl

theorem cell23_1905654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1905654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905654 prefixEnd_1905654 := by exact prefixLift 1905654
  have htrace : WordTrace (prefixWord ++ tailWord_1905654) baseStart_1905654 baseEnd_1905654 := by
    simpa [prefixWord, tailWord_1905654, baseEnd_1905654] using wordTrace_append hprefix tailTrace_1905654
  have hstable : (prefixWord ++ tailWord_1905654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905654).length < 2 ^ (prefixWord ++ tailWord_1905654).sum := by decide
  have hdescent : baseEnd_1905654 < baseStart_1905654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905663 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1905663 : Nat := 118140960795 + 1905663 * 2 ^ 59
def prefixEnd_1905663 : Nat := 4983230072969 + 3 ^ 40 * 1905663 * 2
def baseEnd_1905663 : Nat := 978521084489082818448521

theorem tailTrace_1905663 : CollatzResearch.WordTrace tailWord_1905663 prefixEnd_1905663 978521084489082818448521 := by
  unfold tailWord_1905663
  simp only [CollatzResearch.WordTrace]
  refine ⟨69505239695115887174209643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46336826463410591449473095 69505239695115887174209643)
  ·
    refine ⟨104257859542673830761314465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69505239695115887174209643 104257859542673830761314465)
    ·
      refine ⟨78193394657005373070985849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104257859542673830761314465 78193394657005373070985849)
      ·
        refine ⟨58645045992754029803239387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78193394657005373070985849 58645045992754029803239387)
        ·
          refine ⟨87967568989131044704859081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58645045992754029803239387 87967568989131044704859081)
          ·
            refine ⟨65975676741848283528644311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87967568989131044704859081 65975676741848283528644311)
            ·
              refine ⟨98963515112772425292966467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65975676741848283528644311 98963515112772425292966467)
              ·
                refine ⟨148445272669158637939449701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98963515112772425292966467 148445272669158637939449701)
                ·
                  refine ⟨27833488625467244613646819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148445272669158637939449701 27833488625467244613646819)
                  ·
                    refine ⟨41750232938200866920470229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27833488625467244613646819 41750232938200866920470229)
                    ·
                      refine ⟨978521084489082818448521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41750232938200866920470229 978521084489082818448521)
                      ·
                        rfl

theorem cell23_1905663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1905663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905663 prefixEnd_1905663 := by exact prefixLift 1905663
  have htrace : WordTrace (prefixWord ++ tailWord_1905663) baseStart_1905663 baseEnd_1905663 := by
    simpa [prefixWord, tailWord_1905663, baseEnd_1905663] using wordTrace_append hprefix tailTrace_1905663
  have hstable : (prefixWord ++ tailWord_1905663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905663).length < 2 ^ (prefixWord ++ tailWord_1905663).sum := by decide
  have hdescent : baseEnd_1905663 < baseStart_1905663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905674 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 6]
def baseStart_1905674 : Nat := 118140960795 + 1905674 * 2 ^ 59
def prefixEnd_1905674 : Nat := 4983230072969 + 3 ^ 40 * 1905674 * 2
def baseEnd_1905674 : Nat := 108725192530698030601219

theorem tailTrace_1905674 : CollatzResearch.WordTrace tailWord_1905674 prefixEnd_1905674 108725192530698030601219 := by
  unfold tailWord_1905674
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376410224519009013215019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46337093932050690701906717 17376410224519009013215019)
  ·
    refine ⟨26064615336778513519822529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17376410224519009013215019 26064615336778513519822529)
    ·
      refine ⟨19548461502583885139866897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26064615336778513519822529 19548461502583885139866897)
      ·
        refine ⟨14661346126937913854900173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19548461502583885139866897 14661346126937913854900173)
        ·
          refine ⟨5498004797601717695587565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14661346126937913854900173 5498004797601717695587565)
          ·
            refine ⟨2061751799100644135845337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5498004797601717695587565 2061751799100644135845337)
            ·
              refine ⟨1546313849325483101884003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061751799100644135845337 1546313849325483101884003)
              ·
                refine ⟨2319470773988224652826005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546313849325483101884003 2319470773988224652826005)
                ·
                  refine ⟨108725192530698030601219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2319470773988224652826005 108725192530698030601219)
                  ·
                    rfl

theorem cell23_1905674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_1905674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905674 prefixEnd_1905674 := by exact prefixLift 1905674
  have htrace : WordTrace (prefixWord ++ tailWord_1905674) baseStart_1905674 baseEnd_1905674 := by
    simpa [prefixWord, tailWord_1905674, baseEnd_1905674] using wordTrace_append hprefix tailTrace_1905674
  have hstable : (prefixWord ++ tailWord_1905674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905674).length < 2 ^ (prefixWord ++ tailWord_1905674).sum := by decide
  have hdescent : baseEnd_1905674 < baseStart_1905674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905687 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 3, 5]
def baseStart_1905687 : Nat := 118140960795 + 1905687 * 2 ^ 59
def prefixEnd_1905687 : Nat := 4983230072969 + 3 ^ 40 * 1905687 * 2
def baseEnd_1905687 : Nat := 326177802674930241516137

theorem tailTrace_1905687 : CollatzResearch.WordTrace tailWord_1905687 prefixEnd_1905687 326177802674930241516137 := by
  unfold tailWord_1905687
  simp only [CollatzResearch.WordTrace]
  refine ⟨69506115047028939273083315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46337410031352626182055543 69506115047028939273083315)
  ·
    refine ⟨104259172570543408909624973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69506115047028939273083315 104259172570543408909624973)
    ·
      refine ⟨39097189713953778341109365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104259172570543408909624973 39097189713953778341109365)
      ·
        refine ⟨3665361535683166719479003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39097189713953778341109365 3665361535683166719479003)
        ·
          refine ⟨5498042303524750079218505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665361535683166719479003 5498042303524750079218505)
          ·
            refine ⟨4123531727643562559413879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5498042303524750079218505 4123531727643562559413879)
            ·
              refine ⟨6185297591465343839120819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123531727643562559413879 6185297591465343839120819)
              ·
                refine ⟨9277946387198015758681229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185297591465343839120819 9277946387198015758681229)
                ·
                  refine ⟨3479229895199255909505461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9277946387198015758681229 3479229895199255909505461)
                  ·
                    refine ⟨326177802674930241516137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3479229895199255909505461 326177802674930241516137)
                    ·
                      rfl

theorem cell23_1905687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_1905687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905687 prefixEnd_1905687 := by exact prefixLift 1905687
  have htrace : WordTrace (prefixWord ++ tailWord_1905687) baseStart_1905687 baseEnd_1905687 := by
    simpa [prefixWord, tailWord_1905687, baseEnd_1905687] using wordTrace_append hprefix tailTrace_1905687
  have hstable : (prefixWord ++ tailWord_1905687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905687).length < 2 ^ (prefixWord ++ tailWord_1905687).sum := by decide
  have hdescent : baseEnd_1905687 < baseStart_1905687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905718 : List Nat := [5, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_1905718 : Nat := 118140960795 + 1905718 * 2 ^ 59
def prefixEnd_1905718 : Nat := 4983230072969 + 3 ^ 40 * 1905718 * 2
def baseEnd_1905718 : Nat := 978549325925080103260769

theorem tailTrace_1905718 : CollatzResearch.WordTrace tailWord_1905718 prefixEnd_1905718 978549325925080103260769 := by
  unfold tailWord_1905718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344202856869789472966363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46338163806611087711641205 4344202856869789472966363)
  ·
    refine ⟨6516304285304684209449545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4344202856869789472966363 6516304285304684209449545)
    ·
      refine ⟨4887228213978513157087159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6516304285304684209449545 4887228213978513157087159)
      ·
        refine ⟨7330842320967769735630739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4887228213978513157087159 7330842320967769735630739)
        ·
          refine ⟨10996263481451654603446109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330842320967769735630739 10996263481451654603446109)
          ·
            refine ⟨4123598805544370476292291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10996263481451654603446109 4123598805544370476292291)
            ·
              refine ⟨6185398208316555714438437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123598805544370476292291 6185398208316555714438437)
              ·
                refine ⟨1159762164059354196457207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6185398208316555714438437 1159762164059354196457207)
                ·
                  refine ⟨1739643246089031294685811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159762164059354196457207 1739643246089031294685811)
                  ·
                    refine ⟨2609464869133546942028717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1739643246089031294685811 2609464869133546942028717)
                    ·
                      refine ⟨978549325925080103260769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2609464869133546942028717 978549325925080103260769)
                      ·
                        rfl

theorem cell23_1905718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_1905718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905718 prefixEnd_1905718 := by exact prefixLift 1905718
  have htrace : WordTrace (prefixWord ++ tailWord_1905718) baseStart_1905718 baseEnd_1905718 := by
    simpa [prefixWord, tailWord_1905718, baseEnd_1905718] using wordTrace_append hprefix tailTrace_1905718
  have hstable : (prefixWord ++ tailWord_1905718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905718).length < 2 ^ (prefixWord ++ tailWord_1905718).sum := by decide
  have hdescent : baseEnd_1905718 < baseStart_1905718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905734 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1905734 : Nat := 118140960795 + 1905734 * 2 ^ 59
def prefixEnd_1905734 : Nat := 4983230072969 + 3 ^ 40 * 1905734 * 2
def baseEnd_1905734 : Nat := 326185847205184013553565

theorem tailTrace_1905734 : CollatzResearch.WordTrace tailWord_1905734 prefixEnd_1905734 326185847205184013553565 := by
  unfold tailWord_1905734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172119664933083321876383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46338552851905777533362837 2172119664933083321876383)
  ·
    refine ⟨3258179497399624982814575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2172119664933083321876383 3258179497399624982814575)
    ·
      refine ⟨4887269246099437474221863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258179497399624982814575 4887269246099437474221863)
      ·
        refine ⟨7330903869149156211332795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4887269246099437474221863 7330903869149156211332795)
        ·
          refine ⟨10996355803723734316999193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330903869149156211332795 10996355803723734316999193)
          ·
            refine ⟨8247266852792800737749395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10996355803723734316999193 8247266852792800737749395)
            ·
              refine ⟨12370900279189201106624093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247266852792800737749395 12370900279189201106624093)
              ·
                refine ⟨4639087604695950414984035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12370900279189201106624093 4639087604695950414984035)
                ·
                  refine ⟨6958631407043925622476053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639087604695950414984035 6958631407043925622476053)
                  ·
                    refine ⟨326185847205184013553565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6958631407043925622476053 326185847205184013553565)
                    ·
                      rfl

theorem cell23_1905734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1905734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905734 prefixEnd_1905734 := by exact prefixLift 1905734
  have htrace : WordTrace (prefixWord ++ tailWord_1905734) baseStart_1905734 baseEnd_1905734 := by
    simpa [prefixWord, tailWord_1905734, baseEnd_1905734] using wordTrace_append hprefix tailTrace_1905734
  have hstable : (prefixWord ++ tailWord_1905734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905734).length < 2 ^ (prefixWord ++ tailWord_1905734).sum := by decide
  have hdescent : baseEnd_1905734 < baseStart_1905734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905741 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_1905741 : Nat := 118140960795 + 1905741 * 2 ^ 59
def prefixEnd_1905741 : Nat := 4983230072969 + 3 ^ 40 * 1905741 * 2
def baseEnd_1905741 : Nat := 978561135980133513273163

theorem tailTrace_1905741 : CollatzResearch.WordTrace tailWord_1905741 prefixEnd_1905741 978561135980133513273163 := by
  unfold tailWord_1905741
  simp only [CollatzResearch.WordTrace]
  refine ⟨69508084588833306495549077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46338723059222204330366051 69508084588833306495549077)
  ·
    refine ⟨3258191465101561241978863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69508084588833306495549077 3258191465101561241978863)
    ·
      refine ⟨4887287197652341862968295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258191465101561241978863 4887287197652341862968295)
      ·
        refine ⟨7330930796478512794452443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4887287197652341862968295 7330930796478512794452443)
        ·
          refine ⟨10996396194717769191678665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330930796478512794452443 10996396194717769191678665)
          ·
            refine ⟨8247297146038326893758999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10996396194717769191678665 8247297146038326893758999)
            ·
              refine ⟨12370945719057490340638499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247297146038326893758999 12370945719057490340638499)
              ·
                refine ⟨18556418578586235510957749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12370945719057490340638499 18556418578586235510957749)
                ·
                  refine ⟨1739664241742459579152289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18556418578586235510957749 1739664241742459579152289)
                  ·
                    refine ⟨1304748181306844684364217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1739664241742459579152289 1304748181306844684364217)
                    ·
                      refine ⟨978561135980133513273163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304748181306844684364217 978561135980133513273163)
                      ·
                        rfl

theorem cell23_1905741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_1905741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905741 prefixEnd_1905741 := by exact prefixLift 1905741
  have htrace : WordTrace (prefixWord ++ tailWord_1905741) baseStart_1905741 baseEnd_1905741 := by
    simpa [prefixWord, tailWord_1905741, baseEnd_1905741] using wordTrace_append hprefix tailTrace_1905741
  have hstable : (prefixWord ++ tailWord_1905741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905741).length < 2 ^ (prefixWord ++ tailWord_1905741).sum := by decide
  have hdescent : baseEnd_1905741 < baseStart_1905741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905758 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1905758 : Nat := 118140960795 + 1905758 * 2 ^ 59
def prefixEnd_1905758 : Nat := 4983230072969 + 3 ^ 40 * 1905758 * 2
def baseEnd_1905758 : Nat := 978569865151259946760585

theorem tailTrace_1905758 : CollatzResearch.WordTrace tailWord_1905758 prefixEnd_1905758 978569865151259946760585 := by
  unfold tailWord_1905758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8688588078721464799864741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46339136419847812265945285 8688588078721464799864741)
  ·
    refine ⟨1629110264760274649974639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8688588078721464799864741 1629110264760274649974639)
    ·
      refine ⟨2443665397140411974961959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629110264760274649974639 2443665397140411974961959)
      ·
        refine ⟨3665498095710617962442939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443665397140411974961959 3665498095710617962442939)
        ·
          refine ⟨5498247143565926943664409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665498095710617962442939 5498247143565926943664409)
          ·
            refine ⟨4123685357674445207748307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5498247143565926943664409 4123685357674445207748307)
            ·
              refine ⟨6185528036511667811622461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123685357674445207748307 6185528036511667811622461)
              ·
                refine ⟨2319573013691875429358423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6185528036511667811622461 2319573013691875429358423)
                ·
                  refine ⟨3479359520537813144037635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319573013691875429358423 3479359520537813144037635)
                  ·
                    refine ⟨5219039280806719716056453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3479359520537813144037635 5219039280806719716056453)
                    ·
                      refine ⟨978569865151259946760585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5219039280806719716056453 978569865151259946760585)
                      ·
                        rfl

theorem cell23_1905758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1905758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905758 prefixEnd_1905758 := by exact prefixLift 1905758
  have htrace : WordTrace (prefixWord ++ tailWord_1905758) baseStart_1905758 baseEnd_1905758 := by
    simpa [prefixWord, tailWord_1905758, baseEnd_1905758] using wordTrace_append hprefix tailTrace_1905758
  have hstable : (prefixWord ++ tailWord_1905758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905758).length < 2 ^ (prefixWord ++ tailWord_1905758).sum := by decide
  have hdescent : baseEnd_1905758 < baseStart_1905758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905768 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1905768 : Nat := 118140960795 + 1905768 * 2 ^ 59
def prefixEnd_1905768 : Nat := 4983230072969 + 3 ^ 40 * 1905768 * 2
def baseEnd_1905768 : Nat := 326191666652601635878513

theorem tailTrace_1905768 : CollatzResearch.WordTrace tailWord_1905768 prefixEnd_1905768 326191666652601635878513 := by
  unfold tailWord_1905768
  simp only [CollatzResearch.WordTrace]
  refine ⟨34754534679867745053390979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46339379573156993404521305 34754534679867745053390979)
  ·
    refine ⟨52131802019801617580086469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34754534679867745053390979 52131802019801617580086469)
    ·
      refine ⟨9774712878712803296266213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52131802019801617580086469 9774712878712803296266213)
      ·
        refine ⟨1832758664758650618049915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9774712878712803296266213 1832758664758650618049915)
        ·
          refine ⟨2749137997137975927074873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832758664758650618049915 2749137997137975927074873)
          ·
            refine ⟨2061853497853481945306155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2749137997137975927074873 2061853497853481945306155)
            ·
              refine ⟨3092780246780222917959233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061853497853481945306155 3092780246780222917959233)
              ·
                refine ⟨2319585185085167188469425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092780246780222917959233 2319585185085167188469425)
                ·
                  refine ⟨1739688888813875391352069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2319585185085167188469425 1739688888813875391352069)
                  ·
                    refine ⟨326191666652601635878513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1739688888813875391352069 326191666652601635878513)
                    ·
                      rfl

theorem cell23_1905768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1905768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905768 prefixEnd_1905768 := by exact prefixLift 1905768
  have htrace : WordTrace (prefixWord ++ tailWord_1905768) baseStart_1905768 baseEnd_1905768 := by
    simpa [prefixWord, tailWord_1905768, baseEnd_1905768] using wordTrace_append hprefix tailTrace_1905768
  have hstable : (prefixWord ++ tailWord_1905768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905768).length < 2 ^ (prefixWord ++ tailWord_1905768).sum := by decide
  have hdescent : baseEnd_1905768 < baseStart_1905768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905801 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 1, 3, 2]
def baseStart_1905801 : Nat := 118140960795 + 1905801 * 2 ^ 59
def prefixEnd_1905801 : Nat := 4983230072969 + 3 ^ 40 * 1905801 * 2
def baseEnd_1905801 : Nat := 978591944819403278522887

theorem tailTrace_1905801 : CollatzResearch.WordTrace tailWord_1905801 prefixEnd_1905801 978591944819403278522887 := by
  unfold tailWord_1905801
  simp only [CollatzResearch.WordTrace]
  refine ⟨69510272968615936742733257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46340181979077291161822171 69510272968615936742733257)
  ·
    refine ⟨52132704726461952557049943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69510272968615936742733257 52132704726461952557049943)
    ·
      refine ⟨78199057089692928835574915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52132704726461952557049943 78199057089692928835574915)
      ·
        refine ⟨117298585634539393253362373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78199057089692928835574915 117298585634539393253362373)
        ·
          refine ⟨21993484806476136235005445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117298585634539393253362373 21993484806476136235005445)
          ·
            refine ⟨4123778401214275544063521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21993484806476136235005445 4123778401214275544063521)
            ·
              refine ⟨3092833800910706658047641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123778401214275544063521 3092833800910706658047641)
              ·
                refine ⟨2319625350683029993535731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092833800910706658047641 2319625350683029993535731)
                ·
                  refine ⟨3479438026024544990303597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319625350683029993535731 3479438026024544990303597)
                  ·
                    refine ⟨1304789259759204371363849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479438026024544990303597 1304789259759204371363849)
                    ·
                      refine ⟨978591944819403278522887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304789259759204371363849 978591944819403278522887)
                      ·
                        rfl

theorem cell23_1905801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 3, 2].length) (baseStart_1905801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905801 prefixEnd_1905801 := by exact prefixLift 1905801
  have htrace : WordTrace (prefixWord ++ tailWord_1905801) baseStart_1905801 baseEnd_1905801 := by
    simpa [prefixWord, tailWord_1905801, baseEnd_1905801] using wordTrace_append hprefix tailTrace_1905801
  have hstable : (prefixWord ++ tailWord_1905801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905801).length < 2 ^ (prefixWord ++ tailWord_1905801).sum := by decide
  have hdescent : baseEnd_1905801 < baseStart_1905801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905847 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1905847 : Nat := 118140960795 + 1905847 * 2 ^ 59
def prefixEnd_1905847 : Nat := 4983230072969 + 3 ^ 40 * 1905847 * 2
def baseEnd_1905847 : Nat := 978615564929510098547675

theorem tailTrace_1905847 : CollatzResearch.WordTrace tailWord_1905847 prefixEnd_1905847 978615564929510098547675 := by
  unfold tailWord_1905847
  simp only [CollatzResearch.WordTrace]
  refine ⟨69511950726449286598907795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46341300484299524399271863 69511950726449286598907795)
  ·
    refine ⟨104267926089673929898361693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69511950726449286598907795 104267926089673929898361693)
    ·
      refine ⟨39100472283627723711885635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104267926089673929898361693 39100472283627723711885635)
      ·
        refine ⟨58650708425441585567828453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39100472283627723711885635 58650708425441585567828453)
        ·
          refine ⟨10997007829770297293967835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58650708425441585567828453 10997007829770297293967835)
          ·
            refine ⟨16495511744655445940951753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997007829770297293967835 16495511744655445940951753)
            ·
              refine ⟨12371633808491584455713815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16495511744655445940951753 12371633808491584455713815)
              ·
                refine ⟨18557450712737376683570723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12371633808491584455713815 18557450712737376683570723)
                ·
                  refine ⟨27836176069106065025356085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18557450712737376683570723 27836176069106065025356085)
                  ·
                    refine ⟨2609641506478693596127133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27836176069106065025356085 2609641506478693596127133)
                    ·
                      refine ⟨978615564929510098547675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2609641506478693596127133 978615564929510098547675)
                      ·
                        rfl

theorem cell23_1905847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1905847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905847 prefixEnd_1905847 := by exact prefixLift 1905847
  have htrace : WordTrace (prefixWord ++ tailWord_1905847) baseStart_1905847 baseEnd_1905847 := by
    simpa [prefixWord, tailWord_1905847, baseEnd_1905847] using wordTrace_append hprefix tailTrace_1905847
  have hstable : (prefixWord ++ tailWord_1905847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905847).length < 2 ^ (prefixWord ++ tailWord_1905847).sum := by decide
  have hdescent : baseEnd_1905847 < baseStart_1905847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905914 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_1905914 : Nat := 118140960795 + 1905914 * 2 ^ 59
def prefixEnd_1905914 : Nat := 4983230072969 + 3 ^ 40 * 1905914 * 2
def baseEnd_1905914 : Nat := 326216656044453778803289

theorem tailTrace_1905914 : CollatzResearch.WordTrace tailWord_1905914 prefixEnd_1905914 326216656044453778803289 := by
  unfold tailWord_1905914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17378598604301639260399199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46342929611471038027731197 17378598604301639260399199)
  ·
    refine ⟨26067897906452458890598799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17378598604301639260399199 26067897906452458890598799)
    ·
      refine ⟨39101846859678688335898199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26067897906452458890598799 39101846859678688335898199)
      ·
        refine ⟨58652770289518032503847299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39101846859678688335898199 58652770289518032503847299)
        ·
          refine ⟨87979155434277048755770949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58652770289518032503847299 87979155434277048755770949)
          ·
            refine ⟨16496091643926946641707053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87979155434277048755770949 16496091643926946641707053)
            ·
              refine ⟨6186034366472604990640145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16496091643926946641707053 6186034366472604990640145)
              ·
                refine ⟨4639525774854453742980109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6186034366472604990640145 4639525774854453742980109)
                ·
                  refine ⟨1739822165570420153617541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4639525774854453742980109 1739822165570420153617541)
                  ·
                    refine ⟨326216656044453778803289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1739822165570420153617541 326216656044453778803289)
                    ·
                      rfl

theorem cell23_1905914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_1905914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905914 prefixEnd_1905914 := by exact prefixLift 1905914
  have htrace : WordTrace (prefixWord ++ tailWord_1905914) baseStart_1905914 baseEnd_1905914 := by
    simpa [prefixWord, tailWord_1905914, baseEnd_1905914] using wordTrace_append hprefix tailTrace_1905914
  have hstable : (prefixWord ++ tailWord_1905914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905914).length < 2 ^ (prefixWord ++ tailWord_1905914).sum := by decide
  have hdescent : baseEnd_1905914 < baseStart_1905914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905921 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_1905921 : Nat := 118140960795 + 1905921 * 2 ^ 59
def prefixEnd_1905921 : Nat := 4983230072969 + 3 ^ 40 * 1905921 * 2
def baseEnd_1905921 : Nat := 978653562497942809022335

theorem tailTrace_1905921 : CollatzResearch.WordTrace tailWord_1905921 prefixEnd_1905921 978653562497942809022335 := by
  unfold tailWord_1905921
  simp only [CollatzResearch.WordTrace]
  refine ⟨69514649728181197237101617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46343099818787464824734411 69514649728181197237101617)
  ·
    refine ⟨52135987296135897927826213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69514649728181197237101617 52135987296135897927826213)
    ·
      refine ⟨9775497618025480861467415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52135987296135897927826213 9775497618025480861467415)
      ·
        refine ⟨14663246427038221292201123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9775497618025480861467415 14663246427038221292201123)
        ·
          refine ⟨21994869640557331938301685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14663246427038221292201123 21994869640557331938301685)
          ·
            refine ⟨2062019028802249869215783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21994869640557331938301685 2062019028802249869215783)
            ·
              refine ⟨3093028543203374803823675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062019028802249869215783 3093028543203374803823675)
              ·
                refine ⟨4639542814805062205735513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093028543203374803823675 4639542814805062205735513)
                ·
                  refine ⟨3479657111103796654301635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4639542814805062205735513 3479657111103796654301635)
                  ·
                    refine ⟨5219485666655694981452453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3479657111103796654301635 5219485666655694981452453)
                    ·
                      refine ⟨978653562497942809022335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5219485666655694981452453 978653562497942809022335)
                      ·
                        rfl

theorem cell23_1905921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_1905921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905921 prefixEnd_1905921 := by exact prefixLift 1905921
  have htrace : WordTrace (prefixWord ++ tailWord_1905921) baseStart_1905921 baseEnd_1905921 := by
    simpa [prefixWord, tailWord_1905921, baseEnd_1905921] using wordTrace_append hprefix tailTrace_1905921
  have hstable : (prefixWord ++ tailWord_1905921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905921).length < 2 ^ (prefixWord ++ tailWord_1905921).sum := by decide
  have hdescent : baseEnd_1905921 < baseStart_1905921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905931 : List Nat := [1, 1, 1, 1, 5, 3, 1, 5, 1, 4]
def baseStart_1905931 : Nat := 118140960795 + 1905931 * 2 ^ 59
def prefixEnd_1905931 : Nat := 4983230072969 + 3 ^ 40 * 1905931 * 2
def baseEnd_1905931 : Nat := 326219565768162589965763

theorem tailTrace_1905931 : CollatzResearch.WordTrace tailWord_1905931 prefixEnd_1905931 326219565768162589965763 := by
  unfold tailWord_1905931
  simp only [CollatzResearch.WordTrace]
  refine ⟨69515014458144968944965647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46343342972096645963310431 69515014458144968944965647)
  ·
    refine ⟨104272521687217453417448471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69515014458144968944965647 104272521687217453417448471)
    ·
      refine ⟨156408782530826180126172707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104272521687217453417448471 156408782530826180126172707)
      ·
        refine ⟨234613173796239270189259061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156408782530826180126172707 234613173796239270189259061)
        ·
          refine ⟨21994985043397431580243037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234613173796239270189259061 21994985043397431580243037)
          ·
            refine ⟨8248119391274036842591139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21994985043397431580243037 8248119391274036842591139)
            ·
              refine ⟨12372179086911055263886709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8248119391274036842591139 12372179086911055263886709)
              ·
                refine ⟨1159891789397911430989379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12372179086911055263886709 1159891789397911430989379)
                ·
                  refine ⟨1739837684096867146484069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159891789397911430989379 1739837684096867146484069)
                  ·
                    refine ⟨326219565768162589965763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1739837684096867146484069 326219565768162589965763)
                    ·
                      rfl

theorem cell23_1905931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 4].length) (baseStart_1905931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905931 prefixEnd_1905931 := by exact prefixLift 1905931
  have htrace : WordTrace (prefixWord ++ tailWord_1905931) baseStart_1905931 baseEnd_1905931 := by
    simpa [prefixWord, tailWord_1905931, baseEnd_1905931] using wordTrace_append hprefix tailTrace_1905931
  have hstable : (prefixWord ++ tailWord_1905931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905931).length < 2 ^ (prefixWord ++ tailWord_1905931).sum := by decide
  have hdescent : baseEnd_1905931 < baseStart_1905931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905944 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 6]
def baseStart_1905944 : Nat := 118140960795 + 1905944 * 2 ^ 59
def prefixEnd_1905944 : Nat := 4983230072969 + 3 ^ 40 * 1905944 * 2
def baseEnd_1905944 : Nat := 108740596950332913226081

theorem tailTrace_1905944 : CollatzResearch.WordTrace tailWord_1905944 prefixEnd_1905944 108740596950332913226081 := by
  unfold tailWord_1905944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34757744303548936082594443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46343659071398581443459257 34757744303548936082594443)
  ·
    refine ⟨52136616455323404123891665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34757744303548936082594443 52136616455323404123891665)
    ·
      refine ⟨39102462341492553092918749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52136616455323404123891665 39102462341492553092918749)
      ·
        refine ⟨14663423378059707409844531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39102462341492553092918749 14663423378059707409844531)
        ·
          refine ⟨21995135067089561114766797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14663423378059707409844531 21995135067089561114766797)
          ·
            refine ⟨8248175650158585418037549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21995135067089561114766797 8248175650158585418037549)
            ·
              refine ⟨3093065868809469531764081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8248175650158585418037549 3093065868809469531764081)
              ·
                refine ⟨2319799401607102148823061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3093065868809469531764081 2319799401607102148823061)
                ·
                  refine ⟨108740596950332913226081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2319799401607102148823061 108740596950332913226081)
                  ·
                    rfl

theorem cell23_1905944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 6].length) (baseStart_1905944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905944 prefixEnd_1905944 := by exact prefixLift 1905944
  have htrace : WordTrace (prefixWord ++ tailWord_1905944) baseStart_1905944 baseEnd_1905944 := by
    simpa [prefixWord, tailWord_1905944, baseEnd_1905944] using wordTrace_append hprefix tailTrace_1905944
  have hstable : (prefixWord ++ tailWord_1905944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905944).length < 2 ^ (prefixWord ++ tailWord_1905944).sum := by decide
  have hdescent : baseEnd_1905944 < baseStart_1905944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905971 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 3]
def baseStart_1905971 : Nat := 118140960795 + 1905971 * 2 ^ 59
def prefixEnd_1905971 : Nat := 4983230072969 + 3 ^ 40 * 1905971 * 2
def baseEnd_1905971 : Nat := 978679236530667613397105

theorem tailTrace_1905971 : CollatzResearch.WordTrace tailWord_1905971 prefixEnd_1905971 978679236530667613397105 := by
  unfold tailWord_1905971
  simp only [CollatzResearch.WordTrace]
  refine ⟨69516473378000055776421767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46344315585333370517614511 69516473378000055776421767)
  ·
    refine ⟨104274710067000083664632651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69516473378000055776421767 104274710067000083664632651)
    ·
      refine ⟨156412065100500125496948977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104274710067000083664632651 156412065100500125496948977)
      ·
        refine ⟨117309048825375094122711733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156412065100500125496948977 117309048825375094122711733)
        ·
          refine ⟨10997723327378915074004225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117309048825375094122711733 10997723327378915074004225)
          ·
            refine ⟨8248292495534186305503169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10997723327378915074004225 8248292495534186305503169)
            ·
              refine ⟨6186219371650639729127377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8248292495534186305503169 6186219371650639729127377)
              ·
                refine ⟨4639664528737979796845533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6186219371650639729127377 4639664528737979796845533)
                ·
                  refine ⟨1739874198276742423817075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4639664528737979796845533 1739874198276742423817075)
                  ·
                    refine ⟨2609811297415113635725613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1739874198276742423817075 2609811297415113635725613)
                    ·
                      refine ⟨978679236530667613397105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2609811297415113635725613 978679236530667613397105)
                      ·
                        rfl

theorem cell23_1905971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 3].length) (baseStart_1905971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905971 prefixEnd_1905971 := by exact prefixLift 1905971
  have htrace : WordTrace (prefixWord ++ tailWord_1905971) baseStart_1905971 baseEnd_1905971 := by
    simpa [prefixWord, tailWord_1905971, baseEnd_1905971] using wordTrace_append hprefix tailTrace_1905971
  have hstable : (prefixWord ++ tailWord_1905971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905971).length < 2 ^ (prefixWord ++ tailWord_1905971).sum := by decide
  have hdescent : baseEnd_1905971 < baseStart_1905971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905987 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 3, 6]
def baseStart_1905987 : Nat := 118140960795 + 1905987 * 2 ^ 59
def prefixEnd_1905987 : Nat := 4983230072969 + 3 ^ 40 * 1905987 * 2
def baseEnd_1905987 : Nat := 326229150740379850265677

theorem tailTrace_1905987 : CollatzResearch.WordTrace tailWord_1905987 prefixEnd_1905987 326229150740379850265677 := by
  unfold tailWord_1905987
  simp only [CollatzResearch.WordTrace]
  refine ⟨69517056945942090509004215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46344704630628060339336143 69517056945942090509004215)
  ·
    refine ⟨104275585418913135763506323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69517056945942090509004215 104275585418913135763506323)
    ·
      refine ⟨156413378128369703645259485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104275585418913135763506323 156413378128369703645259485)
      ·
        refine ⟨58655016798138638866972307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156413378128369703645259485 58655016798138638866972307)
        ·
          refine ⟨87982525197207958300458461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58655016798138638866972307 87982525197207958300458461)
          ·
            refine ⟨32993446948952984362671923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87982525197207958300458461 32993446948952984362671923)
            ·
              refine ⟨49490170423429476544007885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32993446948952984362671923 49490170423429476544007885)
              ·
                refine ⟨18558813908786053704002957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49490170423429476544007885 18558813908786053704002957)
                ·
                  refine ⟨6959555215794770139001109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18558813908786053704002957 6959555215794770139001109)
                  ·
                    refine ⟨326229150740379850265677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6959555215794770139001109 326229150740379850265677)
                    ·
                      rfl

theorem cell23_1905987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 6].length) (baseStart_1905987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1905987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1905987 prefixEnd_1905987 := by exact prefixLift 1905987
  have htrace : WordTrace (prefixWord ++ tailWord_1905987) baseStart_1905987 baseEnd_1905987 := by
    simpa [prefixWord, tailWord_1905987, baseEnd_1905987] using wordTrace_append hprefix tailTrace_1905987
  have hstable : (prefixWord ++ tailWord_1905987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905987).length < 2 ^ (prefixWord ++ tailWord_1905987).sum := by decide
  have hdescent : baseEnd_1905987 < baseStart_1905987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906021 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_1906021 : Nat := 118140960795 + 1906021 * 2 ^ 59
def prefixEnd_1906021 : Nat := 4983230072969 + 3 ^ 40 * 1906021 * 2
def baseEnd_1906021 : Nat := 326234970187797472590625

theorem tailTrace_1906021 : CollatzResearch.WordTrace tailWord_1906021 prefixEnd_1906021 326234970187797472590625 := by
  unfold tailWord_1906021
  simp only [CollatzResearch.WordTrace]
  refine ⟨69518297027818914315741917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46345531351879276210494611 69518297027818914315741917)
  ·
    refine ⟨26069361385432092868403219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69518297027818914315741917 26069361385432092868403219)
    ·
      refine ⟨39104042078148139302604829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26069361385432092868403219 39104042078148139302604829)
      ·
        refine ⟨14664015779305552238476811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39104042078148139302604829 14664015779305552238476811)
        ·
          refine ⟨21996023668958328357715217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14664015779305552238476811 21996023668958328357715217)
          ·
            refine ⟨16497017751718746268286413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21996023668958328357715217 16497017751718746268286413)
            ·
              refine ⟨6186381656894529850607405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16497017751718746268286413 6186381656894529850607405)
              ·
                refine ⟨2319893121335448693977777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6186381656894529850607405 2319893121335448693977777)
                ·
                  refine ⟨1739919841001586520483333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2319893121335448693977777 1739919841001586520483333)
                  ·
                    refine ⟨326234970187797472590625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1739919841001586520483333 326234970187797472590625)
                    ·
                      rfl

theorem cell23_1906021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_1906021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906021 prefixEnd_1906021 := by exact prefixLift 1906021
  have htrace : WordTrace (prefixWord ++ tailWord_1906021) baseStart_1906021 baseEnd_1906021 := by
    simpa [prefixWord, tailWord_1906021, baseEnd_1906021] using wordTrace_append hprefix tailTrace_1906021
  have hstable : (prefixWord ++ tailWord_1906021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906021).length < 2 ^ (prefixWord ++ tailWord_1906021).sum := by decide
  have hdescent : baseEnd_1906021 < baseStart_1906021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906028 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_1906028 : Nat := 118140960795 + 1906028 * 2 ^ 59
def prefixEnd_1906028 : Nat := 4983230072969 + 3 ^ 40 * 1906028 * 2
def baseEnd_1906028 : Nat := 978708504927973890384343

theorem tailTrace_1906028 : CollatzResearch.WordTrace tailWord_1906028 prefixEnd_1906028 978708504927973890384343 := by
  unfold tailWord_1906028
  simp only [CollatzResearch.WordTrace]
  refine ⟨34759276169396777255623369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46345701559195703007497825 34759276169396777255623369)
  ·
    refine ⟨26069457127047582941717527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34759276169396777255623369 26069457127047582941717527)
    ·
      refine ⟨39104185690571374412576291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26069457127047582941717527 39104185690571374412576291)
      ·
        refine ⟨58656278535857061618864437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39104185690571374412576291 58656278535857061618864437)
        ·
          refine ⟨5499026112736599526768541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58656278535857061618864437 5499026112736599526768541)
          ·
            refine ⟨2062134792276224822538203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5499026112736599526768541 2062134792276224822538203)
            ·
              refine ⟨3093202188414337233807305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062134792276224822538203 3093202188414337233807305)
              ·
                refine ⟨2319901641310752925355479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3093202188414337233807305 2319901641310752925355479)
                ·
                  refine ⟨3479852461966129388033219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319901641310752925355479 3479852461966129388033219)
                  ·
                    refine ⟨5219778692949194082049829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3479852461966129388033219 5219778692949194082049829)
                    ·
                      refine ⟨978708504927973890384343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5219778692949194082049829 978708504927973890384343)
                      ·
                        rfl

theorem cell23_1906028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_1906028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906028 prefixEnd_1906028 := by exact prefixLift 1906028
  have htrace : WordTrace (prefixWord ++ tailWord_1906028) baseStart_1906028 baseEnd_1906028 := by
    simpa [prefixWord, tailWord_1906028, baseEnd_1906028] using wordTrace_append hprefix tailTrace_1906028
  have hstable : (prefixWord ++ tailWord_1906028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906028).length < 2 ^ (prefixWord ++ tailWord_1906028).sum := by decide
  have hdescent : baseEnd_1906028 < baseStart_1906028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906045 : List Nat := [1, 4, 1, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_1906045 : Nat := 118140960795 + 1906045 * 2 ^ 59
def prefixEnd_1906045 : Nat := 4983230072969 + 3 ^ 40 * 1906045 * 2
def baseEnd_1906045 : Nat := 978717234099100323871765

theorem tailTrace_1906045 : CollatzResearch.WordTrace tailWord_1906045 prefixEnd_1906045 978717234099100323871765 := by
  unfold tailWord_1906045
  simp only [CollatzResearch.WordTrace]
  refine ⟨69519172379731966414615589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46346114919821310943077059 69519172379731966414615589)
  ·
    refine ⟨13034844821199743702740423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69519172379731966414615589 13034844821199743702740423)
    ·
      refine ⟨19552267231799615554110635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13034844821199743702740423 19552267231799615554110635)
      ·
        refine ⟨29328400847699423331165953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19552267231799615554110635 29328400847699423331165953)
        ·
          refine ⟨21996300635774567498374465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29328400847699423331165953 21996300635774567498374465)
          ·
            refine ⟨16497225476830925623780849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21996300635774567498374465 16497225476830925623780849)
            ·
              refine ⟨12372919107623194217835637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16497225476830925623780849 12372919107623194217835637)
              ·
                refine ⟨1159961166339674457922091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12372919107623194217835637 1159961166339674457922091)
                ·
                  refine ⟨1739941749509511686883137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159961166339674457922091 1739941749509511686883137)
                  ·
                    refine ⟨1304956312132133765162353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1739941749509511686883137 1304956312132133765162353)
                    ·
                      refine ⟨978717234099100323871765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304956312132133765162353 978717234099100323871765)
                      ·
                        rfl

theorem cell23_1906045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_1906045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906045 prefixEnd_1906045 := by exact prefixLift 1906045
  have htrace : WordTrace (prefixWord ++ tailWord_1906045) baseStart_1906045 baseEnd_1906045 := by
    simpa [prefixWord, tailWord_1906045, baseEnd_1906045] using wordTrace_append hprefix tailTrace_1906045
  have hstable : (prefixWord ++ tailWord_1906045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906045).length < 2 ^ (prefixWord ++ tailWord_1906045).sum := by decide
  have hdescent : baseEnd_1906045 < baseStart_1906045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906047 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 9]
def baseStart_1906047 : Nat := 118140960795 + 1906047 * 2 ^ 59
def prefixEnd_1906047 : Nat := 4983230072969 + 3 ^ 40 * 1906047 * 2
def baseEnd_1906047 : Nat := 326239420353469772015585

theorem tailTrace_1906047 : CollatzResearch.WordTrace tailWord_1906047 prefixEnd_1906047 326239420353469772015585 := by
  unfold tailWord_1906047
  simp only [CollatzResearch.WordTrace]
  refine ⟨69519245325724720756188395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46346163550483147170792263 69519245325724720756188395)
  ·
    refine ⟨104278867988587081134282593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69519245325724720756188395 104278867988587081134282593)
    ·
      refine ⟨78209150991440310850711945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104278867988587081134282593 78209150991440310850711945)
      ·
        refine ⟨58656863243580233138033959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78209150991440310850711945 58656863243580233138033959)
        ·
          refine ⟨87985294865370349707050939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58656863243580233138033959 87985294865370349707050939)
          ·
            refine ⟨131977942298055524560576409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87985294865370349707050939 131977942298055524560576409)
            ·
              refine ⟨98983456723541643420432307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131977942298055524560576409 98983456723541643420432307)
              ·
                refine ⟨148475185085312465130648461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98983456723541643420432307 148475185085312465130648461)
                ·
                  refine ⟨55678194406992174423993173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148475185085312465130648461 55678194406992174423993173)
                  ·
                    refine ⟨326239420353469772015585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55678194406992174423993173 326239420353469772015585)
                    ·
                      rfl

theorem cell23_1906047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_1906047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906047 prefixEnd_1906047 := by exact prefixLift 1906047
  have htrace : WordTrace (prefixWord ++ tailWord_1906047) baseStart_1906047 baseEnd_1906047 := by
    simpa [prefixWord, tailWord_1906047, baseEnd_1906047] using wordTrace_append hprefix tailTrace_1906047
  have hstable : (prefixWord ++ tailWord_1906047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906047).length < 2 ^ (prefixWord ++ tailWord_1906047).sum := by decide
  have hdescent : baseEnd_1906047 < baseStart_1906047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906084 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1906084 : Nat := 118140960795 + 1906084 * 2 ^ 59
def prefixEnd_1906084 : Nat := 4983230072969 + 3 ^ 40 * 1906084 * 2
def baseEnd_1906084 : Nat := 978737259844625671284085

theorem tailTrace_1906084 : CollatzResearch.WordTrace tailWord_1906084 prefixEnd_1906084 978737259844625671284085 := by
  unfold tailWord_1906084
  simp only [CollatzResearch.WordTrace]
  refine ⟨34760297413295338037642653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46347063217727117383523537 34760297413295338037642653)
  ·
    refine ⟨13035111529985751764115995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34760297413295338037642653 13035111529985751764115995)
    ·
      refine ⟨19552667294978627646173993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13035111529985751764115995 19552667294978627646173993)
      ·
        refine ⟨14664500471233970734630495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19552667294978627646173993 14664500471233970734630495)
        ·
          refine ⟨21996750706850956101945743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14664500471233970734630495 21996750706850956101945743)
          ·
            refine ⟨32995126060276434152918615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21996750706850956101945743 32995126060276434152918615)
            ·
              refine ⟨49492689090414651229377923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32995126060276434152918615 49492689090414651229377923)
              ·
                refine ⟨74239033635621976844066885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49492689090414651229377923 74239033635621976844066885)
                ·
                  refine ⟨13919818806679120658262541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74239033635621976844066885 13919818806679120658262541)
                  ·
                    refine ⟨5219932052504670246848453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13919818806679120658262541 5219932052504670246848453)
                    ·
                      refine ⟨978737259844625671284085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5219932052504670246848453 978737259844625671284085)
                      ·
                        rfl

theorem cell23_1906084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1906084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906084 prefixEnd_1906084 := by exact prefixLift 1906084
  have htrace : WordTrace (prefixWord ++ tailWord_1906084) baseStart_1906084 baseEnd_1906084 := by
    simpa [prefixWord, tailWord_1906084, baseEnd_1906084] using wordTrace_append hprefix tailTrace_1906084
  have hstable : (prefixWord ++ tailWord_1906084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906084).length < 2 ^ (prefixWord ++ tailWord_1906084).sum := by decide
  have hdescent : baseEnd_1906084 < baseStart_1906084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906104 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_1906104 : Nat := 118140960795 + 1906104 * 2 ^ 59
def prefixEnd_1906104 : Nat := 4983230072969 + 3 ^ 40 * 1906104 * 2
def baseEnd_1906104 : Nat := 978747529457715593033993

theorem tailTrace_1906104 : CollatzResearch.WordTrace tailWord_1906104 prefixEnd_1906104 978747529457715593033993 := by
  unfold tailWord_1906104
  simp only [CollatzResearch.WordTrace]
  refine ⟨34760662143259109745506683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46347549524345479660675577 34760662143259109745506683)
  ·
    refine ⟨52140993214888664618260025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34760662143259109745506683 52140993214888664618260025)
    ·
      refine ⟨39105744911166498463695019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52140993214888664618260025 39105744911166498463695019)
      ·
        refine ⟨58658617366749747695542529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39105744911166498463695019 58658617366749747695542529)
        ·
          refine ⟨43993963025062310771656897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58658617366749747695542529 43993963025062310771656897)
          ·
            refine ⟨32995472268796733078742673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43993963025062310771656897 32995472268796733078742673)
            ·
              refine ⟨24746604201597549809057005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32995472268796733078742673 24746604201597549809057005)
              ·
                refine ⟨9279976575599081178396377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24746604201597549809057005 9279976575599081178396377)
                ·
                  refine ⟨6959982431699310883797283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9279976575599081178396377 6959982431699310883797283)
                  ·
                    refine ⟨10439973647548966325695925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959982431699310883797283 10439973647548966325695925)
                    ·
                      refine ⟨978747529457715593033993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10439973647548966325695925 978747529457715593033993)
                      ·
                        rfl

theorem cell23_1906104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_1906104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906104 prefixEnd_1906104 := by exact prefixLift 1906104
  have htrace : WordTrace (prefixWord ++ tailWord_1906104) baseStart_1906104 baseEnd_1906104 := by
    simpa [prefixWord, tailWord_1906104, baseEnd_1906104] using wordTrace_append hprefix tailTrace_1906104
  have hstable : (prefixWord ++ tailWord_1906104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906104).length < 2 ^ (prefixWord ++ tailWord_1906104).sum := by decide
  have hdescent : baseEnd_1906104 < baseStart_1906104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906105 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 1, 3, 2]
def baseStart_1906105 : Nat := 118140960795 + 1906105 * 2 ^ 59
def prefixEnd_1906105 : Nat := 4983230072969 + 3 ^ 40 * 1906105 * 2
def baseEnd_1906105 : Nat := 978748042938370089121489

theorem tailTrace_1906105 : CollatzResearch.WordTrace tailWord_1906105 prefixEnd_1906105 978748042938370089121489 := by
  unfold tailWord_1906105
  simp only [CollatzResearch.WordTrace]
  refine ⟨69521360759514596661799769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46347573839676397774533179 69521360759514596661799769)
  ·
    refine ⟨52141020569635947496349827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69521360759514596661799769 52141020569635947496349827)
    ·
      refine ⟨78211530854453921244524741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52141020569635947496349827 78211530854453921244524741)
      ·
        refine ⟨14664662035210110233348389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78211530854453921244524741 14664662035210110233348389)
        ·
          refine ⟨2749624131601895668752823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14664662035210110233348389 2749624131601895668752823)
          ·
            refine ⟨4124436197402843503129235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749624131601895668752823 4124436197402843503129235)
            ·
              refine ⟨6186654296104265254693853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124436197402843503129235 6186654296104265254693853)
              ·
                refine ⟨2319995361039099470510195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6186654296104265254693853 2319995361039099470510195)
                ·
                  refine ⟨3479993041558649205765293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319995361039099470510195 3479993041558649205765293)
                  ·
                    refine ⟨1304997390584493452161985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479993041558649205765293 1304997390584493452161985)
                    ·
                      refine ⟨978748042938370089121489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1304997390584493452161985 978748042938370089121489)
                      ·
                        rfl

theorem cell23_1906105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_1906105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906105 prefixEnd_1906105 := by exact prefixLift 1906105
  have htrace : WordTrace (prefixWord ++ tailWord_1906105) baseStart_1906105 baseEnd_1906105 := by
    simpa [prefixWord, tailWord_1906105, baseEnd_1906105] using wordTrace_append hprefix tailTrace_1906105
  have hstable : (prefixWord ++ tailWord_1906105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906105).length < 2 ^ (prefixWord ++ tailWord_1906105).sum := by decide
  have hdescent : baseEnd_1906105 < baseStart_1906105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906141 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 7]
def baseStart_1906141 : Nat := 118140960795 + 1906141 * 2 ^ 59
def prefixEnd_1906141 : Nat := 4983230072969 + 3 ^ 40 * 1906141 * 2
def baseEnd_1906141 : Nat := 108751836471325772030147

theorem tailTrace_1906141 : CollatzResearch.WordTrace tailWord_1906141 prefixEnd_1906141 108751836471325772030147 := by
  unfold tailWord_1906141
  simp only [CollatzResearch.WordTrace]
  refine ⟨69522673787384174810110277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46348449191589449873406851 69522673787384174810110277)
  ·
    refine ⟨13035501335134532776895677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69522673787384174810110277 13035501335134532776895677)
    ·
      refine ⟨4888313000675449791335879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13035501335134532776895677 4888313000675449791335879)
      ·
        refine ⟨7332469501013174687003819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4888313000675449791335879 7332469501013174687003819)
        ·
          refine ⟨10998704251519762030505729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332469501013174687003819 10998704251519762030505729)
          ·
            refine ⟨8249028188639821522879297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998704251519762030505729 8249028188639821522879297)
            ·
              refine ⟨6186771141479866142159473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249028188639821522879297 6186771141479866142159473)
              ·
                refine ⟨4640078356109899606619605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6186771141479866142159473 4640078356109899606619605)
                ·
                  refine ⟨108751836471325772030147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4640078356109899606619605 108751836471325772030147)
                  ·
                    rfl

theorem cell23_1906141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_1906141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906141 prefixEnd_1906141 := by exact prefixLift 1906141
  have htrace : WordTrace (prefixWord ++ tailWord_1906141) baseStart_1906141 baseEnd_1906141 := by
    simpa [prefixWord, tailWord_1906141, baseEnd_1906141] using wordTrace_append hprefix tailTrace_1906141
  have hstable : (prefixWord ++ tailWord_1906141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906141).length < 2 ^ (prefixWord ++ tailWord_1906141).sum := by decide
  have hdescent : baseEnd_1906141 < baseStart_1906141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906208 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1906208 : Nat := 118140960795 + 1906208 * 2 ^ 59
def prefixEnd_1906208 : Nat := 4983230072969 + 3 ^ 40 * 1906208 * 2
def baseEnd_1906208 : Nat := 978800931445783186133515

theorem tailTrace_1906208 : CollatzResearch.WordTrace tailWord_1906208 prefixEnd_1906208 978800931445783186133515 := by
  unfold tailWord_1906208
  simp only [CollatzResearch.WordTrace]
  refine ⟨34762558739070722626399639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46350078318760963501866185 34762558739070722626399639)
  ·
    refine ⟨52143838108606083939599459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34762558739070722626399639 52143838108606083939599459)
    ·
      refine ⟨78215757162909125909399189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52143838108606083939599459 78215757162909125909399189)
      ·
        refine ⟨3666363617011365277003087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78215757162909125909399189 3666363617011365277003087)
        ·
          refine ⟨5499545425517047915504631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666363617011365277003087 5499545425517047915504631)
          ·
            refine ⟨8249318138275571873256947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499545425517047915504631 8249318138275571873256947)
            ·
              refine ⟨12373977207413357809885421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8249318138275571873256947 12373977207413357809885421)
              ·
                refine ⟨4640241452780009178707033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12373977207413357809885421 4640241452780009178707033)
                ·
                  refine ⟨3480181089585006884030275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4640241452780009178707033 3480181089585006884030275)
                  ·
                    refine ⟨5220271634377510326045413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3480181089585006884030275 5220271634377510326045413)
                    ·
                      refine ⟨978800931445783186133515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5220271634377510326045413 978800931445783186133515)
                      ·
                        rfl

theorem cell23_1906208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1906208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906208 prefixEnd_1906208 := by exact prefixLift 1906208
  have htrace : WordTrace (prefixWord ++ tailWord_1906208) baseStart_1906208 baseEnd_1906208 := by
    simpa [prefixWord, tailWord_1906208, baseEnd_1906208] using wordTrace_append hprefix tailTrace_1906208
  have hstable : (prefixWord ++ tailWord_1906208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906208).length < 2 ^ (prefixWord ++ tailWord_1906208).sum := by decide
  have hdescent : baseEnd_1906208 < baseStart_1906208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906231 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 6]
def baseStart_1906231 : Nat := 118140960795 + 1906231 * 2 ^ 59
def prefixEnd_1906231 : Nat := 4983230072969 + 3 ^ 40 * 1906231 * 2
def baseEnd_1906231 : Nat := 108756971277870732905101

theorem tailTrace_1906231 : CollatzResearch.WordTrace tailWord_1906231 prefixEnd_1906231 108756971277870732905101 := by
  unfold tailWord_1906231
  simp only [CollatzResearch.WordTrace]
  refine ⟨69525956357058120180886547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46350637571372080120591031 69525956357058120180886547)
  ·
    refine ⟨104288934535587180271329821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69525956357058120180886547 104288934535587180271329821)
    ·
      refine ⟨39108350450845192601748683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104288934535587180271329821 39108350450845192601748683)
      ·
        refine ⟨58662525676267788902623025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39108350450845192601748683 58662525676267788902623025)
        ·
          refine ⟨43996894257200841676967269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58662525676267788902623025 43996894257200841676967269)
          ·
            refine ⟨8249417673225157814431363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43996894257200841676967269 8249417673225157814431363)
            ·
              refine ⟨12374126509837736721647045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8249417673225157814431363 12374126509837736721647045)
              ·
                refine ⟨2320148720594575635308821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12374126509837736721647045 2320148720594575635308821)
                ·
                  refine ⟨108756971277870732905101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2320148720594575635308821 108756971277870732905101)
                  ·
                    rfl

theorem cell23_1906231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 6].length) (baseStart_1906231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906231 prefixEnd_1906231 := by exact prefixLift 1906231
  have htrace : WordTrace (prefixWord ++ tailWord_1906231) baseStart_1906231 baseEnd_1906231 := by
    simpa [prefixWord, tailWord_1906231, baseEnd_1906231] using wordTrace_append hprefix tailTrace_1906231
  have hstable : (prefixWord ++ tailWord_1906231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906231).length < 2 ^ (prefixWord ++ tailWord_1906231).sum := by decide
  have hdescent : baseEnd_1906231 < baseStart_1906231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906312 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 1, 5]
def baseStart_1906312 : Nat := 118140960795 + 1906312 * 2 ^ 59
def prefixEnd_1906312 : Nat := 4983230072969 + 3 ^ 40 * 1906312 * 2
def baseEnd_1906312 : Nat := 326284777811283593077679

theorem tailTrace_1906312 : CollatzResearch.WordTrace tailWord_1906312 prefixEnd_1906312 326284777811283593077679 := by
  unfold tailWord_1906312
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764455334882335507292595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46352607113176447343056793 34764455334882335507292595)
  ·
    refine ⟨52146683002323503260938893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34764455334882335507292595 52146683002323503260938893)
    ·
      refine ⟨19555006125871313722852085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52146683002323503260938893 19555006125871313722852085)
      ·
        refine ⟨1833281824300435661517383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19555006125871313722852085 1833281824300435661517383)
        ·
          refine ⟨2749922736450653492276075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833281824300435661517383 2749922736450653492276075)
          ·
            refine ⟨4124884104675980238414113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749922736450653492276075 4124884104675980238414113)
            ·
              refine ⟨3093663078506985178810585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4124884104675980238414113 3093663078506985178810585)
              ·
                refine ⟨2320247308880238884107939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3093663078506985178810585 2320247308880238884107939)
                ·
                  refine ⟨3480370963320358326161909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320247308880238884107939 3480370963320358326161909)
                  ·
                    refine ⟨326284777811283593077679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3480370963320358326161909 326284777811283593077679)
                    ·
                      rfl

theorem cell23_1906312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_1906312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906312 prefixEnd_1906312 := by exact prefixLift 1906312
  have htrace : WordTrace (prefixWord ++ tailWord_1906312) baseStart_1906312 baseEnd_1906312 := by
    simpa [prefixWord, tailWord_1906312, baseEnd_1906312] using wordTrace_append hprefix tailTrace_1906312
  have hstable : (prefixWord ++ tailWord_1906312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906312).length < 2 ^ (prefixWord ++ tailWord_1906312).sum := by decide
  have hdescent : baseEnd_1906312 < baseStart_1906312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906315 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 3, 2, 2]
def baseStart_1906315 : Nat := 118140960795 + 1906315 * 2 ^ 59
def prefixEnd_1906315 : Nat := 4983230072969 + 3 ^ 40 * 1906315 * 2
def baseEnd_1906315 : Nat := 978855873875814267495523

theorem tailTrace_1906315 : CollatzResearch.WordTrace tailWord_1906315 prefixEnd_1906315 978855873875814267495523 := by
  unfold tailWord_1906315
  simp only [CollatzResearch.WordTrace]
  refine ⟨69529020088753802526944399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46352680059169201684629599 69529020088753802526944399)
  ·
    refine ⟨104293530133130703790416599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69529020088753802526944399 104293530133130703790416599)
    ·
      refine ⟨156440295199696055685624899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104293530133130703790416599 156440295199696055685624899)
      ·
        refine ⟨234660442799544083528437349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156440295199696055685624899 234660442799544083528437349)
        ·
          refine ⟨43998833024914515661582003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234660442799544083528437349 43998833024914515661582003)
          ·
            refine ⟨65998249537371773492373005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43998833024914515661582003 65998249537371773492373005)
            ·
              refine ⟨24749343576514415059639877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65998249537371773492373005 24749343576514415059639877)
              ·
                refine ⟨4640501920596452823682477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24749343576514415059639877 4640501920596452823682477)
                ·
                  refine ⟨1740188220223669808880929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4640501920596452823682477 1740188220223669808880929)
                  ·
                    refine ⟨1305141165167752356660697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1740188220223669808880929 1305141165167752356660697)
                    ·
                      refine ⟨978855873875814267495523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305141165167752356660697 978855873875814267495523)
                      ·
                        rfl

theorem cell23_1906315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 2, 2].length) (baseStart_1906315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906315 prefixEnd_1906315 := by exact prefixLift 1906315
  have htrace : WordTrace (prefixWord ++ tailWord_1906315) baseStart_1906315 baseEnd_1906315 := by
    simpa [prefixWord, tailWord_1906315, baseEnd_1906315] using wordTrace_append hprefix tailTrace_1906315
  have hstable : (prefixWord ++ tailWord_1906315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906315).length < 2 ^ (prefixWord ++ tailWord_1906315).sum := by decide
  have hdescent : baseEnd_1906315 < baseStart_1906315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906351 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 2, 7]
def baseStart_1906351 : Nat := 118140960795 + 1906351 * 2 ^ 59
def prefixEnd_1906351 : Nat := 4983230072969 + 3 ^ 40 * 1906351 * 2
def baseEnd_1906351 : Nat := 326291453059792042215119

theorem tailTrace_1906351 : CollatzResearch.WordTrace tailWord_1906351 prefixEnd_1906351 326291453059792042215119 := by
  unfold tailWord_1906351
  simp only [CollatzResearch.WordTrace]
  refine ⟨69530333116623380675254907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46353555411082253783503271 69530333116623380675254907)
  ·
    refine ⟨104295499674935071012882361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69530333116623380675254907 104295499674935071012882361)
    ·
      refine ⟨78221624756201303259661771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104295499674935071012882361 78221624756201303259661771)
      ·
        refine ⟨117332437134301954889492657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78221624756201303259661771 117332437134301954889492657)
        ·
          refine ⟨87999327850726466167119493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117332437134301954889492657 87999327850726466167119493)
          ·
            refine ⟨16499873972011212406334905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87999327850726466167119493 16499873972011212406334905)
            ·
              refine ⟨12374905479008409304751179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16499873972011212406334905 12374905479008409304751179)
              ·
                refine ⟨18562358218512613957126769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12374905479008409304751179 18562358218512613957126769)
                ·
                  refine ⟨13921768663884460467845077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18562358218512613957126769 13921768663884460467845077)
                  ·
                    refine ⟨326291453059792042215119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13921768663884460467845077 326291453059792042215119)
                    ·
                      rfl

theorem cell23_1906351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_1906351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906351 prefixEnd_1906351 := by exact prefixLift 1906351
  have htrace : WordTrace (prefixWord ++ tailWord_1906351) baseStart_1906351 baseEnd_1906351 := by
    simpa [prefixWord, tailWord_1906351, baseEnd_1906351] using wordTrace_append hprefix tailTrace_1906351
  have hstable : (prefixWord ++ tailWord_1906351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906351).length < 2 ^ (prefixWord ++ tailWord_1906351).sum := by decide
  have hdescent : baseEnd_1906351 < baseStart_1906351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906375 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_1906375 : Nat := 118140960795 + 1906375 * 2 ^ 59
def prefixEnd_1906375 : Nat := 4983230072969 + 3 ^ 40 * 1906375 * 2
def baseEnd_1906375 : Nat := 978886682715084032745247

theorem tailTrace_1906375 : CollatzResearch.WordTrace tailWord_1906375 prefixEnd_1906375 978886682715084032745247 := by
  unfold tailWord_1906375
  simp only [CollatzResearch.WordTrace]
  refine ⟨69531208468536432774128579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46354138979024288516085719 69531208468536432774128579)
  ·
    refine ⟨104296812702804649161192869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69531208468536432774128579 104296812702804649161192869)
    ·
      refine ⟨19555652381775871717723663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104296812702804649161192869 19555652381775871717723663)
      ·
        refine ⟨29333478572663807576585495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19555652381775871717723663 29333478572663807576585495)
        ·
          refine ⟨44000217858995711364878243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29333478572663807576585495 44000217858995711364878243)
          ·
            refine ⟨66000326788493567047317365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44000217858995711364878243 66000326788493567047317365)
            ·
              refine ⟨6187530636421271910686003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66000326788493567047317365 6187530636421271910686003)
              ·
                refine ⟨9281295954631907866029005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187530636421271910686003 9281295954631907866029005)
                ·
                  refine ⟨3480485982986965449760877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9281295954631907866029005 3480485982986965449760877)
                  ·
                    refine ⟨1305182243620112043660329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3480485982986965449760877 1305182243620112043660329)
                    ·
                      refine ⟨978886682715084032745247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305182243620112043660329 978886682715084032745247)
                      ·
                        rfl

theorem cell23_1906375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_1906375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906375 prefixEnd_1906375 := by exact prefixLift 1906375
  have htrace : WordTrace (prefixWord ++ tailWord_1906375) baseStart_1906375 baseEnd_1906375 := by
    simpa [prefixWord, tailWord_1906375, baseEnd_1906375] using wordTrace_append hprefix tailTrace_1906375
  have hstable : (prefixWord ++ tailWord_1906375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906375).length < 2 ^ (prefixWord ++ tailWord_1906375).sum := by decide
  have hdescent : baseEnd_1906375 < baseStart_1906375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906405 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 3, 4, 2]
def baseStart_1906405 : Nat := 118140960795 + 1906405 * 2 ^ 59
def prefixEnd_1906405 : Nat := 4983230072969 + 3 ^ 40 * 1906405 * 2
def baseEnd_1906405 : Nat := 978902087134718915370109

theorem tailTrace_1906405 : CollatzResearch.WordTrace tailWord_1906405 prefixEnd_1906405 978902087134718915370109 := by
  unfold tailWord_1906405
  simp only [CollatzResearch.WordTrace]
  refine ⟨69532302658427747897720669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46354868438951831931813779 69532302658427747897720669)
  ·
    refine ⟨26074613496910405461645251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69532302658427747897720669 26074613496910405461645251)
    ·
      refine ⟨39111920245365608192467877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26074613496910405461645251 39111920245365608192467877)
      ·
        refine ⟨7333485046006051536087727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39111920245365608192467877 7333485046006051536087727)
        ·
          refine ⟨11000227569009077304131591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7333485046006051536087727 11000227569009077304131591)
          ·
            refine ⟨16500341353513615956197387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000227569009077304131591 16500341353513615956197387)
            ·
              refine ⟨24750512030270423934296081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16500341353513615956197387 24750512030270423934296081)
              ·
                refine ⟨18562884022702817950722061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24750512030270423934296081 18562884022702817950722061)
                ·
                  refine ⟨6961081508513556731520773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18562884022702817950722061 6961081508513556731520773)
                  ·
                    refine ⟨1305202782846291887160145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961081508513556731520773 1305202782846291887160145)
                    ·
                      refine ⟨978902087134718915370109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305202782846291887160145 978902087134718915370109)
                      ·
                        rfl

theorem cell23_1906405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_1906405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906405 prefixEnd_1906405 := by exact prefixLift 1906405
  have htrace : WordTrace (prefixWord ++ tailWord_1906405) baseStart_1906405 baseEnd_1906405 := by
    simpa [prefixWord, tailWord_1906405, baseEnd_1906405] using wordTrace_append hprefix tailTrace_1906405
  have hstable : (prefixWord ++ tailWord_1906405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906405).length < 2 ^ (prefixWord ++ tailWord_1906405).sum := by decide
  have hdescent : baseEnd_1906405 < baseStart_1906405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906422 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_1906422 : Nat := 118140960795 + 1906422 * 2 ^ 59
def prefixEnd_1906422 : Nat := 4983230072969 + 3 ^ 40 * 1906422 * 2
def baseEnd_1906422 : Nat := 978910816305845348857531

theorem tailTrace_1906422 : CollatzResearch.WordTrace tailWord_1906422 prefixEnd_1906422 978910816305845348857531 := by
  unfold tailWord_1906422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345807668710384987568095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46355281799577439867393013 4345807668710384987568095)
  ·
    refine ⟨6518711503065577481352143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4345807668710384987568095 6518711503065577481352143)
    ·
      refine ⟨9778067254598366222028215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6518711503065577481352143 9778067254598366222028215)
      ·
        refine ⟨14667100881897549333042323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9778067254598366222028215 14667100881897549333042323)
        ·
          refine ⟨22000651322846323999563485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14667100881897549333042323 22000651322846323999563485)
          ·
            refine ⟨8250244246067371499836307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22000651322846323999563485 8250244246067371499836307)
            ·
              refine ⟨12375366369101057249754461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8250244246067371499836307 12375366369101057249754461)
              ·
                refine ⟨4640762388412896468657923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12375366369101057249754461 4640762388412896468657923)
                ·
                  refine ⟨6961143582619344702986885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640762388412896468657923 6961143582619344702986885)
                  ·
                    refine ⟨1305214421741127131810041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961143582619344702986885 1305214421741127131810041)
                    ·
                      refine ⟨978910816305845348857531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305214421741127131810041 978910816305845348857531)
                      ·
                        rfl

theorem cell23_1906422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_1906422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906422 prefixEnd_1906422 := by exact prefixLift 1906422
  have htrace : WordTrace (prefixWord ++ tailWord_1906422) baseStart_1906422 baseEnd_1906422 := by
    simpa [prefixWord, tailWord_1906422, baseEnd_1906422] using wordTrace_append hprefix tailTrace_1906422
  have hstable : (prefixWord ++ tailWord_1906422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906422).length < 2 ^ (prefixWord ++ tailWord_1906422).sum := by decide
  have hdescent : baseEnd_1906422 < baseStart_1906422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906428 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 7]
def baseStart_1906428 : Nat := 118140960795 + 1906428 * 2 ^ 59
def prefixEnd_1906428 : Nat := 4983230072969 + 3 ^ 40 * 1906428 * 2
def baseEnd_1906428 : Nat := 108768210798863591709167

theorem tailTrace_1906428 : CollatzResearch.WordTrace tailWord_1906428 prefixEnd_1906428 108768210798863591709167 := by
  unfold tailWord_1906428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34766570768672211412903969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46355427691562948550538625 34766570768672211412903969)
  ·
    refine ⟨26074928076504158559677977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34766570768672211412903969 26074928076504158559677977)
    ·
      refine ⟨19556196057378118919758483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26074928076504158559677977 19556196057378118919758483)
      ·
        refine ⟨29334294086067178379637725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19556196057378118919758483 29334294086067178379637725)
        ·
          refine ⟨11000360282275191892364147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29334294086067178379637725 11000360282275191892364147)
          ·
            refine ⟨16500540423412787838546221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000360282275191892364147 16500540423412787838546221)
            ·
              refine ⟨6187702658779795439454833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16500540423412787838546221 6187702658779795439454833)
              ·
                refine ⟨4640776994084846579591125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187702658779795439454833 4640776994084846579591125)
                ·
                  refine ⟨108768210798863591709167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4640776994084846579591125 108768210798863591709167)
                  ·
                    rfl

theorem cell23_1906428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_1906428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906428 prefixEnd_1906428 := by exact prefixLift 1906428
  have htrace : WordTrace (prefixWord ++ tailWord_1906428) baseStart_1906428 baseEnd_1906428 := by
    simpa [prefixWord, tailWord_1906428, baseEnd_1906428] using wordTrace_append hprefix tailTrace_1906428
  have hstable : (prefixWord ++ tailWord_1906428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906428).length < 2 ^ (prefixWord ++ tailWord_1906428).sum := by decide
  have hdescent : baseEnd_1906428 < baseStart_1906428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906455 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1906455 : Nat := 118140960795 + 1906455 * 2 ^ 59
def prefixEnd_1906455 : Nat := 4983230072969 + 3 ^ 40 * 1906455 * 2
def baseEnd_1906455 : Nat := 978927761167443719744879

theorem tailTrace_1906455 : CollatzResearch.WordTrace tailWord_1906455 prefixEnd_1906455 978927761167443719744879 := by
  unfold tailWord_1906455
  simp only [CollatzResearch.WordTrace]
  refine ⟨69534126308246606437040819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46356084205497737624693879 69534126308246606437040819)
  ·
    refine ⟨104301189462369909655561229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69534126308246606437040819 104301189462369909655561229)
    ·
      refine ⟨39112946048388716120835461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104301189462369909655561229 39112946048388716120835461)
      ·
        refine ⟨7333677384072884272656649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39112946048388716120835461 7333677384072884272656649)
        ·
          refine ⟨5500258038054663204492487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7333677384072884272656649 5500258038054663204492487)
          ·
            refine ⟨8250387057081994806738731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500258038054663204492487 8250387057081994806738731)
            ·
              refine ⟨12375580585622992210108097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8250387057081994806738731 12375580585622992210108097)
              ·
                refine ⟨9281685439217244157581073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12375580585622992210108097 9281685439217244157581073)
                ·
                  refine ⟨6961264079412933118185805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9281685439217244157581073 6961264079412933118185805)
                  ·
                    refine ⟨2610474029779849919319677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6961264079412933118185805 2610474029779849919319677)
                    ·
                      refine ⟨978927761167443719744879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2610474029779849919319677 978927761167443719744879)
                      ·
                        rfl

theorem cell23_1906455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1906455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906455 prefixEnd_1906455 := by exact prefixLift 1906455
  have htrace : WordTrace (prefixWord ++ tailWord_1906455) baseStart_1906455 baseEnd_1906455 := by
    simpa [prefixWord, tailWord_1906455, baseEnd_1906455] using wordTrace_append hprefix tailTrace_1906455
  have hstable : (prefixWord ++ tailWord_1906455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906455).length < 2 ^ (prefixWord ++ tailWord_1906455).sum := by decide
  have hdescent : baseEnd_1906455 < baseStart_1906455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906535 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 6]
def baseStart_1906535 : Nat := 118140960795 + 1906535 * 2 ^ 59
def prefixEnd_1906535 : Nat := 4983230072969 + 3 ^ 40 * 1906535 * 2
def baseEnd_1906535 : Nat := 108774315513311489638279

theorem tailTrace_1906535 : CollatzResearch.WordTrace tailWord_1906535 prefixEnd_1906535 108774315513311489638279 := by
  unfold tailWord_1906535
  simp only [CollatzResearch.WordTrace]
  refine ⟨69537044147956780099953059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46358029431971186733302039 69537044147956780099953059)
  ·
    refine ⟨104305566221935170149929589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69537044147956780099953059 104305566221935170149929589)
    ·
      refine ⟨9778646833306422201555899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104305566221935170149929589 9778646833306422201555899)
      ·
        refine ⟨14667970249959633302333849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9778646833306422201555899 14667970249959633302333849)
        ·
          refine ⟨11000977687469724976750387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14667970249959633302333849 11000977687469724976750387)
          ·
            refine ⟨16501466531204587465125581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000977687469724976750387 16501466531204587465125581)
            ·
              refine ⟨6188049949201720299422093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16501466531204587465125581 6188049949201720299422093)
              ·
                refine ⟨2320518730950645112283285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6188049949201720299422093 2320518730950645112283285)
                ·
                  refine ⟨108774315513311489638279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2320518730950645112283285 108774315513311489638279)
                  ·
                    rfl

theorem cell23_1906535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 6].length) (baseStart_1906535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906535 prefixEnd_1906535 := by exact prefixLift 1906535
  have htrace : WordTrace (prefixWord ++ tailWord_1906535) baseStart_1906535 baseEnd_1906535 := by
    simpa [prefixWord, tailWord_1906535, baseEnd_1906535] using wordTrace_append hprefix tailTrace_1906535
  have hstable : (prefixWord ++ tailWord_1906535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906535).length < 2 ^ (prefixWord ++ tailWord_1906535).sum := by decide
  have hdescent : baseEnd_1906535 < baseStart_1906535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906585 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_1906585 : Nat := 118140960795 + 1906585 * 2 ^ 59
def prefixEnd_1906585 : Nat := 4983230072969 + 3 ^ 40 * 1906585 * 2
def baseEnd_1906585 : Nat := 978994513652528211119281

theorem tailTrace_1906585 : CollatzResearch.WordTrace tailWord_1906585 prefixEnd_1906585 978994513652528211119281 := by
  unfold tailWord_1906585
  simp only [CollatzResearch.WordTrace]
  refine ⟨69538867797775638639273209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46359245198517092426182139 69538867797775638639273209)
  ·
    refine ⟨52154150848331728979454907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69538867797775638639273209 52154150848331728979454907)
    ·
      refine ⟨78231226272497593469182361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52154150848331728979454907 78231226272497593469182361)
      ·
        refine ⟨58673419704373195101886771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78231226272497593469182361 58673419704373195101886771)
        ·
          refine ⟨88010129556559792652830157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58673419704373195101886771 88010129556559792652830157)
          ·
            refine ⟨33003798583709922244811309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88010129556559792652830157 33003798583709922244811309)
            ·
              refine ⟨12376424468891220841804241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33003798583709922244811309 12376424468891220841804241)
              ·
                refine ⟨9282318351668415631353181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12376424468891220841804241 9282318351668415631353181)
                ·
                  refine ⟨3480869381875655861757443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9282318351668415631353181 3480869381875655861757443)
                  ·
                    refine ⟨5221304072813483792636165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3480869381875655861757443 5221304072813483792636165)
                    ·
                      refine ⟨978994513652528211119281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5221304072813483792636165 978994513652528211119281)
                      ·
                        rfl

theorem cell23_1906585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_1906585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906585 prefixEnd_1906585 := by exact prefixLift 1906585
  have htrace : WordTrace (prefixWord ++ tailWord_1906585) baseStart_1906585 baseEnd_1906585 := by
    simpa [prefixWord, tailWord_1906585, baseEnd_1906585] using wordTrace_append hprefix tailTrace_1906585
  have hstable : (prefixWord ++ tailWord_1906585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906585).length < 2 ^ (prefixWord ++ tailWord_1906585).sum := by decide
  have hdescent : baseEnd_1906585 < baseStart_1906585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906595 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 6, 4]
def baseStart_1906595 : Nat := 118140960795 + 1906595 * 2 ^ 59
def prefixEnd_1906595 : Nat := 4983230072969 + 3 ^ 40 * 1906595 * 2
def baseEnd_1906595 : Nat := 326333216153024390664745

theorem tailTrace_1906595 : CollatzResearch.WordTrace tailWord_1906595 prefixEnd_1906595 326333216153024390664745 := by
  unfold tailWord_1906595
  simp only [CollatzResearch.WordTrace]
  refine ⟨69539232527739410347137239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46359488351826273564758159 69539232527739410347137239)
  ·
    refine ⟨104308848791609115520705859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69539232527739410347137239 104308848791609115520705859)
    ·
      refine ⟨156463273187413673281058789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104308848791609115520705859 156463273187413673281058789)
      ·
        refine ⟨29336863722640063740198523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156463273187413673281058789 29336863722640063740198523)
        ·
          refine ⟨44005295583960095610297785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29336863722640063740198523 44005295583960095610297785)
          ·
            refine ⟨33003971687970071707723339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44005295583960095610297785 33003971687970071707723339)
            ·
              refine ⟨49505957531955107561585009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33003971687970071707723339 49505957531955107561585009)
              ·
                refine ⟨37129468148966330671188757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49505957531955107561585009 37129468148966330671188757)
                ·
                  refine ⟨1740443819482796750211973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37129468148966330671188757 1740443819482796750211973)
                  ·
                    refine ⟨326333216153024390664745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1740443819482796750211973 326333216153024390664745)
                    ·
                      rfl

theorem cell23_1906595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 4].length) (baseStart_1906595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906595 prefixEnd_1906595 := by exact prefixLift 1906595
  have htrace : WordTrace (prefixWord ++ tailWord_1906595) baseStart_1906595 baseEnd_1906595 := by
    simpa [prefixWord, tailWord_1906595, baseEnd_1906595] using wordTrace_append hprefix tailTrace_1906595
  have hstable : (prefixWord ++ tailWord_1906595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906595).length < 2 ^ (prefixWord ++ tailWord_1906595).sum := by decide
  have hdescent : baseEnd_1906595 < baseStart_1906595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906636 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 3, 2, 2]
def baseStart_1906636 : Nat := 118140960795 + 1906636 * 2 ^ 59
def prefixEnd_1906636 : Nat := 4983230072969 + 3 ^ 40 * 1906636 * 2
def baseEnd_1906636 : Nat := 979020701165907511581547

theorem tailTrace_1906636 : CollatzResearch.WordTrace tailWord_1906636 prefixEnd_1906636 979020701165907511581547 := by
  unfold tailWord_1906636
  simp only [CollatzResearch.WordTrace]
  refine ⟨34770363960295437174689881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46360485280393916232919841 34770363960295437174689881)
  ·
    refine ⟨26077772970221577881017411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34770363960295437174689881 26077772970221577881017411)
    ·
      refine ⟨39116659455332366821526117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26077772970221577881017411 39116659455332366821526117)
      ·
        refine ⟨7334373647874818779036147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39116659455332366821526117 7334373647874818779036147)
        ·
          refine ⟨11001560471812228168554221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334373647874818779036147 11001560471812228168554221)
          ·
            refine ⟨4125585176929585563207833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11001560471812228168554221 4125585176929585563207833)
            ·
              refine ⟨3094188882697189172405875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4125585176929585563207833 3094188882697189172405875)
              ·
                refine ⟨4641283324045783758608813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094188882697189172405875 4641283324045783758608813)
                ·
                  refine ⟨1740481246517168909478305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4641283324045783758608813 1740481246517168909478305)
                  ·
                    refine ⟨1305360934887876682108729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1740481246517168909478305 1305360934887876682108729)
                    ·
                      refine ⟨979020701165907511581547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305360934887876682108729 979020701165907511581547)
                      ·
                        rfl

theorem cell23_1906636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_1906636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906636 prefixEnd_1906636 := by exact prefixLift 1906636
  have htrace : WordTrace (prefixWord ++ tailWord_1906636) baseStart_1906636 baseEnd_1906636 := by
    simpa [prefixWord, tailWord_1906636, baseEnd_1906636] using wordTrace_append hprefix tailTrace_1906636
  have hstable : (prefixWord ++ tailWord_1906636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906636).length < 2 ^ (prefixWord ++ tailWord_1906636).sum := by decide
  have hdescent : baseEnd_1906636 < baseStart_1906636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906646 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1906646 : Nat := 118140960795 + 1906646 * 2 ^ 59
def prefixEnd_1906646 : Nat := 4983230072969 + 3 ^ 40 * 1906646 * 2
def baseEnd_1906646 : Nat := 326341945324150824152167

theorem tailTrace_1906646 : CollatzResearch.WordTrace tailWord_1906646 prefixEnd_1906646 326341945324150824152167 := by
  unfold tailWord_1906646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346318290659665378577737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46360728433703097371495861 4346318290659665378577737)
  ·
    refine ⟨3259738717994749033933303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4346318290659665378577737 3259738717994749033933303)
    ·
      refine ⟨4889608076992123550899955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3259738717994749033933303 4889608076992123550899955)
      ·
        refine ⟨7334412115488185326349933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889608076992123550899955 7334412115488185326349933)
        ·
          refine ⟨2750404543308069497381225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7334412115488185326349933 2750404543308069497381225)
          ·
            refine ⟨2062803407481052123035919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750404543308069497381225 2062803407481052123035919)
            ·
              refine ⟨3094205111221578184553879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062803407481052123035919 3094205111221578184553879)
              ·
                refine ⟨4641307666832367276830819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094205111221578184553879 4641307666832367276830819)
                ·
                  refine ⟨6961961500248550915246229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641307666832367276830819 6961961500248550915246229)
                  ·
                    refine ⟨326341945324150824152167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6961961500248550915246229 326341945324150824152167)
                    ·
                      rfl

theorem cell23_1906646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1906646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906646 prefixEnd_1906646 := by exact prefixLift 1906646
  have htrace : WordTrace (prefixWord ++ tailWord_1906646) baseStart_1906646 baseEnd_1906646 := by
    simpa [prefixWord, tailWord_1906646, baseEnd_1906646] using wordTrace_append hprefix tailTrace_1906646
  have hstable : (prefixWord ++ tailWord_1906646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906646).length < 2 ^ (prefixWord ++ tailWord_1906646).sum := by decide
  have hdescent : baseEnd_1906646 < baseStart_1906646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906649 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 4]
def baseStart_1906649 : Nat := 118140960795 + 1906649 * 2 ^ 59
def prefixEnd_1906649 : Nat := 4983230072969 + 3 ^ 40 * 1906649 * 2
def baseEnd_1906649 : Nat := 979027376414415960718987

theorem tailTrace_1906649 : CollatzResearch.WordTrace tailWord_1906649 prefixEnd_1906649 979027376414415960718987 := by
  unfold tailWord_1906649
  simp only [CollatzResearch.WordTrace]
  refine ⟨69541202069543777569603001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46360801379695851713068667 69541202069543777569603001)
  ·
    refine ⟨52155901552157833177202251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69541202069543777569603001 52155901552157833177202251)
    ·
      refine ⟨78233852328236749765803377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52155901552157833177202251 78233852328236749765803377)
      ·
        refine ⟨58675389246177562324352533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78233852328236749765803377 58675389246177562324352533)
        ·
          refine ⟨2750408870914573233954025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58675389246177562324352533 2750408870914573233954025)
          ·
            refine ⟨2062806653185929925465519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750408870914573233954025 2062806653185929925465519)
            ·
              refine ⟨3094209979778894888198279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062806653185929925465519 3094209979778894888198279)
              ·
                refine ⟨4641314969668342332297419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094209979778894888198279 4641314969668342332297419)
                ·
                  refine ⟨6961972454502513498446129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641314969668342332297419 6961972454502513498446129)
                  ·
                    refine ⟨5221479340876885123834597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6961972454502513498446129 5221479340876885123834597)
                    ·
                      refine ⟨979027376414415960718987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5221479340876885123834597 979027376414415960718987)
                      ·
                        rfl

theorem cell23_1906649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_1906649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906649 prefixEnd_1906649 := by exact prefixLift 1906649
  have htrace : WordTrace (prefixWord ++ tailWord_1906649) baseStart_1906649 baseEnd_1906649 := by
    simpa [prefixWord, tailWord_1906649, baseEnd_1906649] using wordTrace_append hprefix tailTrace_1906649
  have hstable : (prefixWord ++ tailWord_1906649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906649).length < 2 ^ (prefixWord ++ tailWord_1906649).sum := by decide
  have hdescent : baseEnd_1906649 < baseStart_1906649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906670 : List Nat := [4, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_1906670 : Nat := 118140960795 + 1906670 * 2 ^ 59
def prefixEnd_1906670 : Nat := 4983230072969 + 3 ^ 40 * 1906670 * 2
def baseEnd_1906670 : Nat := 979038159508160378556391

theorem tailTrace_1906670 : CollatzResearch.WordTrace tailWord_1906670 prefixEnd_1906670 979038159508160378556391 := by
  unfold tailWord_1906670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8692746000308462269514683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46361312001645132104078309 8692746000308462269514683)
  ·
    refine ⟨13039119000462693404272025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8692746000308462269514683 13039119000462693404272025)
    ·
      refine ⟨9779339250347020053204019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13039119000462693404272025 9779339250347020053204019)
      ·
        refine ⟨14669008875520530079806029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9779339250347020053204019 14669008875520530079806029)
        ·
          refine ⟨5500878328320198779927261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14669008875520530079806029 5500878328320198779927261)
          ·
            refine ⟨2062829373120074542472723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5500878328320198779927261 2062829373120074542472723)
            ·
              refine ⟨3094244059680111813709085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062829373120074542472723 3094244059680111813709085)
              ·
                refine ⟨1160341522380041930140907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3094244059680111813709085 1160341522380041930140907)
                ·
                  refine ⟨1740512283570062895211361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160341522380041930140907 1740512283570062895211361)
                  ·
                    refine ⟨1305384212677547171408521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1740512283570062895211361 1305384212677547171408521)
                    ·
                      refine ⟨979038159508160378556391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305384212677547171408521 979038159508160378556391)
                      ·
                        rfl

theorem cell23_1906670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_1906670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906670 prefixEnd_1906670 := by exact prefixLift 1906670
  have htrace : WordTrace (prefixWord ++ tailWord_1906670) baseStart_1906670 baseEnd_1906670 := by
    simpa [prefixWord, tailWord_1906670, baseEnd_1906670] using wordTrace_append hprefix tailTrace_1906670
  have hstable : (prefixWord ++ tailWord_1906670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906670).length < 2 ^ (prefixWord ++ tailWord_1906670).sum := by decide
  have hdescent : baseEnd_1906670 < baseStart_1906670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906685 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1906685 : Nat := 118140960795 + 1906685 * 2 ^ 59
def prefixEnd_1906685 : Nat := 4983230072969 + 3 ^ 40 * 1906685 * 2
def baseEnd_1906685 : Nat := 326348620572659273289607

theorem tailTrace_1906685 : CollatzResearch.WordTrace tailWord_1906685 prefixEnd_1906685 326348620572659273289607 := by
  unfold tailWord_1906685
  simp only [CollatzResearch.WordTrace]
  refine ⟨69542515097413355717913509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46361676731608903811942339 69542515097413355717913509)
  ·
    refine ⟨13039221580765004197108783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69542515097413355717913509 13039221580765004197108783)
    ·
      refine ⟨19558832371147506295663175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13039221580765004197108783 19558832371147506295663175)
      ·
        refine ⟨29338248556721259443494763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19558832371147506295663175 29338248556721259443494763)
        ·
          refine ⟨44007372835081889165242145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29338248556721259443494763 44007372835081889165242145)
          ·
            refine ⟨33005529626311416873931609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44007372835081889165242145 33005529626311416873931609)
            ·
              refine ⟨24754147219733562655448707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33005529626311416873931609 24754147219733562655448707)
              ·
                refine ⟨37131220829600343983173061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24754147219733562655448707 37131220829600343983173061)
                ·
                  refine ⟨6962103905550064496844949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37131220829600343983173061 6962103905550064496844949)
                  ·
                    refine ⟨326348620572659273289607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6962103905550064496844949 326348620572659273289607)
                    ·
                      rfl

theorem cell23_1906685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1906685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906685 prefixEnd_1906685 := by exact prefixLift 1906685
  have htrace : WordTrace (prefixWord ++ tailWord_1906685) baseStart_1906685 baseEnd_1906685 := by
    simpa [prefixWord, tailWord_1906685, baseEnd_1906685] using wordTrace_append hprefix tailTrace_1906685
  have hstable : (prefixWord ++ tailWord_1906685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906685).length < 2 ^ (prefixWord ++ tailWord_1906685).sum := by decide
  have hdescent : baseEnd_1906685 < baseStart_1906685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906686 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1906686 : Nat := 118140960795 + 1906686 * 2 ^ 59
def prefixEnd_1906686 : Nat := 4983230072969 + 3 ^ 40 * 1906686 * 2
def baseEnd_1906686 : Nat := 979046375198632315956317

theorem tailTrace_1906686 : CollatzResearch.WordTrace tailWord_1906686 prefixEnd_1906686 979046375198632315956317 := by
  unfold tailWord_1906686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8692818946301216611087489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46361701046939821925799941 8692818946301216611087489)
  ·
    refine ⟨6519614209725912458315617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8692818946301216611087489 6519614209725912458315617)
    ·
      refine ⟨4889710657294434343736713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6519614209725912458315617 4889710657294434343736713)
      ·
        refine ⟨3667282992970825757802535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4889710657294434343736713 3667282992970825757802535)
        ·
          refine ⟨5500924489456238636703803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667282992970825757802535 5500924489456238636703803)
          ·
            refine ⟨8251386734184357955055705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500924489456238636703803 8251386734184357955055705)
            ·
              refine ⟨6188540050638268466291779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251386734184357955055705 6188540050638268466291779)
              ·
                refine ⟨9282810075957402699437669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188540050638268466291779 9282810075957402699437669)
                ·
                  refine ⟨1740526889242013006144563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9282810075957402699437669 1740526889242013006144563)
                  ·
                    refine ⟨2610790333863019509216845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1740526889242013006144563 2610790333863019509216845)
                    ·
                      refine ⟨979046375198632315956317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2610790333863019509216845 979046375198632315956317)
                      ·
                        rfl

theorem cell23_1906686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1906686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906686 prefixEnd_1906686 := by exact prefixLift 1906686
  have htrace : WordTrace (prefixWord ++ tailWord_1906686) baseStart_1906686 baseEnd_1906686 := by
    simpa [prefixWord, tailWord_1906686, baseEnd_1906686] using wordTrace_append hprefix tailTrace_1906686
  have hstable : (prefixWord ++ tailWord_1906686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906686).length < 2 ^ (prefixWord ++ tailWord_1906686).sum := by decide
  have hdescent : baseEnd_1906686 < baseStart_1906686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906749 : List Nat := [1, 4, 1, 3, 1, 1, 3, 4, 5]
def baseStart_1906749 : Nat := 118140960795 + 1906749 * 2 ^ 59
def prefixEnd_1906749 : Nat := 4983230072969 + 3 ^ 40 * 1906749 * 2
def baseEnd_1906749 : Nat := 108786524942207285496503

theorem tailTrace_1906749 : CollatzResearch.WordTrace tailWord_1906749 prefixEnd_1906749 108786524942207285496503 := by
  unfold tailWord_1906749
  simp only [CollatzResearch.WordTrace]
  refine ⟨69544849369181494648243301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46363232912787663098828867 69544849369181494648243301)
  ·
    refine ⟨13039659256721530246545619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69544849369181494648243301 13039659256721530246545619)
    ·
      refine ⟨19559488885082295369818429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13039659256721530246545619 19559488885082295369818429)
      ·
        refine ⟨7334808331905860763681911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19559488885082295369818429 7334808331905860763681911)
        ·
          refine ⟨11002212497858791145522867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334808331905860763681911 11002212497858791145522867)
          ·
            refine ⟨16503318746788186718284301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11002212497858791145522867 16503318746788186718284301)
            ·
              refine ⟨6188744530045570019356613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16503318746788186718284301 6188744530045570019356613)
              ·
                refine ⟨1160389599383544378629365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6188744530045570019356613 1160389599383544378629365)
                ·
                  refine ⟨108786524942207285496503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1160389599383544378629365 108786524942207285496503)
                  ·
                    rfl

theorem cell23_1906749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_1906749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906749 prefixEnd_1906749 := by exact prefixLift 1906749
  have htrace : WordTrace (prefixWord ++ tailWord_1906749) baseStart_1906749 baseEnd_1906749 := by
    simpa [prefixWord, tailWord_1906749, baseEnd_1906749] using wordTrace_append hprefix tailTrace_1906749
  have hstable : (prefixWord ++ tailWord_1906749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906749).length < 2 ^ (prefixWord ++ tailWord_1906749).sum := by decide
  have hdescent : baseEnd_1906749 < baseStart_1906749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906755 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7]
def baseStart_1906755 : Nat := 118140960795 + 1906755 * 2 ^ 59
def prefixEnd_1906755 : Nat := 4983230072969 + 3 ^ 40 * 1906755 * 2
def baseEnd_1906755 : Nat := 979081805363792545993499

theorem tailTrace_1906755 : CollatzResearch.WordTrace tailWord_1906755 prefixEnd_1906755 979081805363792545993499 := by
  unfold tailWord_1906755
  simp only [CollatzResearch.WordTrace]
  refine ⟨69545068207159757672961719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46363378804773171781974479 69545068207159757672961719)
  ·
    refine ⟨104317602310739636509442579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69545068207159757672961719 104317602310739636509442579)
    ·
      refine ⟨156476403466109454764163869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104317602310739636509442579 156476403466109454764163869)
      ·
        refine ⟨58678651299791045536561451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156476403466109454764163869 58678651299791045536561451)
        ·
          refine ⟨88017976949686568304842177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58678651299791045536561451 88017976949686568304842177)
          ·
            refine ⟨66013482712264926228631633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88017976949686568304842177 66013482712264926228631633)
            ·
              refine ⟨49510112034198694671473725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66013482712264926228631633 49510112034198694671473725)
              ·
                refine ⟨18566292012824510501802647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49510112034198694671473725 18566292012824510501802647)
                ·
                  refine ⟨27849438019236765752703971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18566292012824510501802647 27849438019236765752703971)
                  ·
                    refine ⟨41774157028855148629055957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27849438019236765752703971 41774157028855148629055957)
                    ·
                      refine ⟨979081805363792545993499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41774157028855148629055957 979081805363792545993499)
                      ·
                        rfl

theorem cell23_1906755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_1906755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906755 prefixEnd_1906755 := by exact prefixLift 1906755
  have htrace : WordTrace (prefixWord ++ tailWord_1906755) baseStart_1906755 baseEnd_1906755 := by
    simpa [prefixWord, tailWord_1906755, baseEnd_1906755] using wordTrace_append hprefix tailTrace_1906755
  have hstable : (prefixWord ++ tailWord_1906755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906755).length < 2 ^ (prefixWord ++ tailWord_1906755).sum := by decide
  have hdescent : baseEnd_1906755 < baseStart_1906755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906799 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 2, 4, 2]
def baseStart_1906799 : Nat := 118140960795 + 1906799 * 2 ^ 59
def prefixEnd_1906799 : Nat := 4983230072969 + 3 ^ 40 * 1906799 * 2
def baseEnd_1906799 : Nat := 979104398512590373843297

theorem tailTrace_1906799 : CollatzResearch.WordTrace tailWord_1906799 prefixEnd_1906799 979104398512590373843297 := by
  unfold tailWord_1906799
  simp only [CollatzResearch.WordTrace]
  refine ⟨69546673019000353187563451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46364448679333568791708967 69546673019000353187563451)
  ·
    refine ⟨104320009528500529781345177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69546673019000353187563451 104320009528500529781345177)
    ·
      refine ⟨78240007146375397336008883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104320009528500529781345177 78240007146375397336008883)
      ·
        refine ⟨117360010719563096004013325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78240007146375397336008883 117360010719563096004013325)
        ·
          refine ⟨44010004019836161001504997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117360010719563096004013325 44010004019836161001504997)
          ·
            refine ⟨8251875753719280187782187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44010004019836161001504997 8251875753719280187782187)
            ·
              refine ⟨12377813630578920281673281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8251875753719280187782187 12377813630578920281673281)
              ·
                refine ⟨9283360222934190211254961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12377813630578920281673281 9283360222934190211254961)
                ·
                  refine ⟨6962520167200642658441221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9283360222934190211254961 6962520167200642658441221)
                  ·
                    refine ⟨1305472531350120498457729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962520167200642658441221 1305472531350120498457729)
                    ·
                      refine ⟨979104398512590373843297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305472531350120498457729 979104398512590373843297)
                      ·
                        rfl

theorem cell23_1906799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4, 2].length) (baseStart_1906799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906799 prefixEnd_1906799 := by exact prefixLift 1906799
  have htrace : WordTrace (prefixWord ++ tailWord_1906799) baseStart_1906799 baseEnd_1906799 := by
    simpa [prefixWord, tailWord_1906799, baseEnd_1906799] using wordTrace_append hprefix tailTrace_1906799
  have hstable : (prefixWord ++ tailWord_1906799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906799).length < 2 ^ (prefixWord ++ tailWord_1906799).sum := by decide
  have hdescent : baseEnd_1906799 < baseStart_1906799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906809 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 3, 4]
def baseStart_1906809 : Nat := 118140960795 + 1906809 * 2 ^ 59
def prefixEnd_1906809 : Nat := 4983230072969 + 3 ^ 40 * 1906809 * 2
def baseEnd_1906809 : Nat := 326369844439711778239417

theorem tailTrace_1906809 : CollatzResearch.WordTrace tailWord_1906809 prefixEnd_1906809 326369844439711778239417 := by
  unfold tailWord_1906809
  simp only [CollatzResearch.WordTrace]
  refine ⟨69547037748964124895427481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46364691832642749930284987 69547037748964124895427481)
  ·
    refine ⟨52160278311723093671570611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69547037748964124895427481 52160278311723093671570611)
    ·
      refine ⟨78240417467584640507355917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52160278311723093671570611 78240417467584640507355917)
      ·
        refine ⟨29340156550344240190258469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78240417467584640507355917 29340156550344240190258469)
        ·
          refine ⟨5501279353189545035673463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29340156550344240190258469 5501279353189545035673463)
          ·
            refine ⟨8251919029784317553510195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501279353189545035673463 8251919029784317553510195)
            ·
              refine ⟨12377878544676476330265293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8251919029784317553510195 12377878544676476330265293)
              ·
                refine ⟨4641704454253678623849485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12377878544676476330265293 4641704454253678623849485)
                ·
                  refine ⟨1740639170345129483943557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4641704454253678623849485 1740639170345129483943557)
                  ·
                    refine ⟨326369844439711778239417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1740639170345129483943557 326369844439711778239417)
                    ·
                      rfl

theorem cell23_1906809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_1906809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906809 prefixEnd_1906809 := by exact prefixLift 1906809
  have htrace : WordTrace (prefixWord ++ tailWord_1906809) baseStart_1906809 baseEnd_1906809 := by
    simpa [prefixWord, tailWord_1906809, baseEnd_1906809] using wordTrace_append hprefix tailTrace_1906809
  have hstable : (prefixWord ++ tailWord_1906809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906809).length < 2 ^ (prefixWord ++ tailWord_1906809).sum := by decide
  have hdescent : baseEnd_1906809 < baseStart_1906809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906832 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3]
def baseStart_1906832 : Nat := 118140960795 + 1906832 * 2 ^ 59
def prefixEnd_1906832 : Nat := 4983230072969 + 3 ^ 40 * 1906832 * 2
def baseEnd_1906832 : Nat := 979121343374188744730645

theorem tailTrace_1906832 : CollatzResearch.WordTrace tailWord_1906832 prefixEnd_1906832 979121343374188744730645 := by
  unfold tailWord_1906832
  simp only [CollatzResearch.WordTrace]
  refine ⟨34773938313940399911757375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46365251085253866549009833 34773938313940399911757375)
  ·
    refine ⟨52160907470910599867636063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34773938313940399911757375 52160907470910599867636063)
    ·
      refine ⟨78241361206365899801454095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52160907470910599867636063 78241361206365899801454095)
      ·
        refine ⟨117362041809548849702181143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78241361206365899801454095 117362041809548849702181143)
        ·
          refine ⟨176043062714323274553271715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117362041809548849702181143 176043062714323274553271715)
          ·
            refine ⟨264064594071484911829907573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176043062714323274553271715 264064594071484911829907573)
            ·
              refine ⟨24756055694201710484053835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264064594071484911829907573 24756055694201710484053835)
              ·
                refine ⟨37134083541302565726080753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24756055694201710484053835 37134083541302565726080753)
                ·
                  refine ⟨27850562655976924294560565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37134083541302565726080753 27850562655976924294560565)
                  ·
                    refine ⟨2610990248997836652615053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27850562655976924294560565 2610990248997836652615053)
                    ·
                      refine ⟨979121343374188744730645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2610990248997836652615053 979121343374188744730645)
                      ·
                        rfl

theorem cell23_1906832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_1906832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906832 prefixEnd_1906832 := by exact prefixLift 1906832
  have htrace : WordTrace (prefixWord ++ tailWord_1906832) baseStart_1906832 baseEnd_1906832 := by
    simpa [prefixWord, tailWord_1906832, baseEnd_1906832] using wordTrace_append hprefix tailTrace_1906832
  have hstable : (prefixWord ++ tailWord_1906832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906832).length < 2 ^ (prefixWord ++ tailWord_1906832).sum := by decide
  have hdescent : baseEnd_1906832 < baseStart_1906832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906889 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 4]
def baseStart_1906889 : Nat := 118140960795 + 1906889 * 2 ^ 59
def prefixEnd_1906889 : Nat := 4983230072969 + 3 ^ 40 * 1906889 * 2
def baseEnd_1906889 : Nat := 979150611771495021717883

theorem tailTrace_1906889 : CollatzResearch.WordTrace tailWord_1906889 prefixEnd_1906889 979150611771495021717883 := by
  unfold tailWord_1906889
  simp only [CollatzResearch.WordTrace]
  refine ⟨69549955588674298558339721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46366637059116199038893147 69549955588674298558339721)
  ·
    refine ⟨52162466691505723918754791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69549955588674298558339721 52162466691505723918754791)
    ·
      refine ⟨78243700037258585878132187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52162466691505723918754791 78243700037258585878132187)
      ·
        refine ⟨117365550055887878817198281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78243700037258585878132187 117365550055887878817198281)
        ·
          refine ⟨88024162541915909112898711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117365550055887878817198281 88024162541915909112898711)
          ·
            refine ⟨132036243812873863669348067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88024162541915909112898711 132036243812873863669348067)
            ·
              refine ⟨198054365719310795504022101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132036243812873863669348067 198054365719310795504022101)
              ·
                refine ⟨2320949598273173384812759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 198054365719310795504022101 2320949598273173384812759)
                ·
                  refine ⟨3481424397409760077219139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320949598273173384812759 3481424397409760077219139)
                  ·
                    refine ⟨5222136596114640115828709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3481424397409760077219139 5222136596114640115828709)
                    ·
                      refine ⟨979150611771495021717883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5222136596114640115828709 979150611771495021717883)
                      ·
                        rfl

theorem cell23_1906889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_1906889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906889 prefixEnd_1906889 := by exact prefixLift 1906889
  have htrace : WordTrace (prefixWord ++ tailWord_1906889) baseStart_1906889 baseEnd_1906889 := by
    simpa [prefixWord, tailWord_1906889, baseEnd_1906889] using wordTrace_append hprefix tailTrace_1906889
  have hstable : (prefixWord ++ tailWord_1906889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906889).length < 2 ^ (prefixWord ++ tailWord_1906889).sum := by decide
  have hdescent : baseEnd_1906889 < baseStart_1906889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906917 : List Nat := [1, 3, 1, 4, 2, 3, 2, 2, 1, 1, 3]
def baseStart_1906917 : Nat := 118140960795 + 1906917 * 2 ^ 59
def prefixEnd_1906917 : Nat := 4983230072969 + 3 ^ 40 * 1906917 * 2
def baseEnd_1906917 : Nat := 979164989229820912167755

theorem tailTrace_1906917 : CollatzResearch.WordTrace tailWord_1906917 prefixEnd_1906917 979164989229820912167755 := by
  unfold tailWord_1906917
  simp only [CollatzResearch.WordTrace]
  refine ⟨69550976832572859340359005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46367317888381906226906003 69550976832572859340359005)
  ·
    refine ⟨26081616312214822252634627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69550976832572859340359005 26081616312214822252634627)
    ·
      refine ⟨39122424468322233378951941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26081616312214822252634627 39122424468322233378951941)
      ·
        refine ⟨7335454587810418758553489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39122424468322233378951941 7335454587810418758553489)
        ·
          refine ⟨5501590940857814068915117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7335454587810418758553489 5501590940857814068915117)
          ·
            refine ⟨2063096602821680275843169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5501590940857814068915117 2063096602821680275843169)
            ·
              refine ⟨1547322452116260206882377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063096602821680275843169 1547322452116260206882377)
              ·
                refine ⟨1160491839087195155161783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547322452116260206882377 1160491839087195155161783)
                ·
                  refine ⟨1740737758630792732742675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160491839087195155161783 1740737758630792732742675)
                  ·
                    refine ⟨2611106637946189099114013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1740737758630792732742675 2611106637946189099114013)
                    ·
                      refine ⟨979164989229820912167755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2611106637946189099114013 979164989229820912167755)
                      ·
                        rfl

theorem cell23_1906917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_1906917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906917 prefixEnd_1906917 := by exact prefixLift 1906917
  have htrace : WordTrace (prefixWord ++ tailWord_1906917) baseStart_1906917 baseEnd_1906917 := by
    simpa [prefixWord, tailWord_1906917, baseEnd_1906917] using wordTrace_append hprefix tailTrace_1906917
  have hstable : (prefixWord ++ tailWord_1906917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906917).length < 2 ^ (prefixWord ++ tailWord_1906917).sum := by decide
  have hdescent : baseEnd_1906917 < baseStart_1906917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906956 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1906956 : Nat := 118140960795 + 1906956 * 2 ^ 59
def prefixEnd_1906956 : Nat := 4983230072969 + 3 ^ 40 * 1906956 * 2
def baseEnd_1906956 : Nat := 979185014975346259580075

theorem tailTrace_1906956 : CollatzResearch.WordTrace tailWord_1906956 prefixEnd_1906956 979185014975346259580075 := by
  unfold tailWord_1906956
  simp only [CollatzResearch.WordTrace]
  refine ⟨34776199639715784500514361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46368266186287712667352481 34776199639715784500514361)
  ·
    refine ⟨26082149729786838375385771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34776199639715784500514361 26082149729786838375385771)
    ·
      refine ⟨39123224594680257563078657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26082149729786838375385771 39123224594680257563078657)
      ·
        refine ⟨29342418446010193172308993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39123224594680257563078657 29342418446010193172308993)
        ·
          refine ⟨22006813834507644879231745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29342418446010193172308993 22006813834507644879231745)
          ·
            refine ⟨16505110375880733659423809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22006813834507644879231745 16505110375880733659423809)
            ·
              refine ⟨12378832781910550244567857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16505110375880733659423809 12378832781910550244567857)
              ·
                refine ⟨9284124586432912683425893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12378832781910550244567857 9284124586432912683425893)
                ·
                  refine ⟨1740773359956171128142355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9284124586432912683425893 1740773359956171128142355)
                  ·
                    refine ⟨2611160039934256692213533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1740773359956171128142355 2611160039934256692213533)
                    ·
                      refine ⟨979185014975346259580075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2611160039934256692213533 979185014975346259580075)
                      ·
                        rfl

theorem cell23_1906956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1906956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906956 prefixEnd_1906956 := by exact prefixLift 1906956
  have htrace : WordTrace (prefixWord ++ tailWord_1906956) baseStart_1906956 baseEnd_1906956 := by
    simpa [prefixWord, tailWord_1906956, baseEnd_1906956] using wordTrace_append hprefix tailTrace_1906956
  have hstable : (prefixWord ++ tailWord_1906956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906956).length < 2 ^ (prefixWord ++ tailWord_1906956).sum := by decide
  have hdescent : baseEnd_1906956 < baseStart_1906956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906974 : List Nat := [4, 3, 2, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1906974 : Nat := 118140960795 + 1906974 * 2 ^ 59
def prefixEnd_1906974 : Nat := 4983230072969 + 3 ^ 40 * 1906974 * 2
def baseEnd_1906974 : Nat := 979194257627127189154993

theorem tailTrace_1906974 : CollatzResearch.WordTrace tailWord_1906974 prefixEnd_1906974 979194257627127189154993 := by
  unfold tailWord_1906974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694131974170794759397997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46368703862244238716789317 8694131974170794759397997)
  ·
    refine ⟨3260299490314048034774249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8694131974170794759397997 3260299490314048034774249)
    ·
      refine ⟨2445224617735536026080687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3260299490314048034774249 2445224617735536026080687)
      ·
        refine ⟨3667836926603304039121031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2445224617735536026080687 3667836926603304039121031)
        ·
          refine ⟨5501755389904956058681547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667836926603304039121031 5501755389904956058681547)
          ·
            refine ⟨8252633084857434088022321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501755389904956058681547 8252633084857434088022321)
            ·
              refine ⟨6189474813643075566016741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8252633084857434088022321 6189474813643075566016741)
              ·
                refine ⟨1160526527558076668628139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6189474813643075566016741 1160526527558076668628139)
                ·
                  refine ⟨1740789791337115002942209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160526527558076668628139 1740789791337115002942209)
                  ·
                    refine ⟨1305592343502836252206657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1740789791337115002942209 1305592343502836252206657)
                    ·
                      refine ⟨979194257627127189154993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305592343502836252206657 979194257627127189154993)
                      ·
                        rfl

theorem cell23_1906974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1906974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906974 prefixEnd_1906974 := by exact prefixLift 1906974
  have htrace : WordTrace (prefixWord ++ tailWord_1906974) baseStart_1906974 baseEnd_1906974 := by
    simpa [prefixWord, tailWord_1906974, baseEnd_1906974] using wordTrace_append hprefix tailTrace_1906974
  have hstable : (prefixWord ++ tailWord_1906974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906974).length < 2 ^ (prefixWord ++ tailWord_1906974).sum := by decide
  have hdescent : baseEnd_1906974 < baseStart_1906974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906999 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1906999 : Nat := 118140960795 + 1906999 * 2 ^ 59
def prefixEnd_1906999 : Nat := 4983230072969 + 3 ^ 40 * 1906999 * 2
def baseEnd_1906999 : Nat := 979207094643489591342377

theorem tailTrace_1906999 : CollatzResearch.WordTrace tailWord_1906999 prefixEnd_1906999 979207094643489591342377 := by
  unfold tailWord_1906999
  simp only [CollatzResearch.WordTrace]
  refine ⟨69553967618275787344844051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46369311745517191563229367 69553967618275787344844051)
  ·
    refine ⟨104330951427413681017266077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69553967618275787344844051 104330951427413681017266077)
    ·
      refine ⟨39124106785280130381474779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104330951427413681017266077 39124106785280130381474779)
      ·
        refine ⟨58686160177920195572212169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39124106785280130381474779 58686160177920195572212169)
        ·
          refine ⟨44014620133440146679159127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58686160177920195572212169 44014620133440146679159127)
          ·
            refine ⟨66021930200160220018738691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44014620133440146679159127 66021930200160220018738691)
            ·
              refine ⟨99032895300240330028108037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66021930200160220018738691 99032895300240330028108037)
              ·
                refine ⟨18568667868795061880270257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99032895300240330028108037 18568667868795061880270257)
                ·
                  refine ⟨13926500901596296410202693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18568667868795061880270257 13926500901596296410202693)
                  ·
                    refine ⟨2611218919049305576913005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13926500901596296410202693 2611218919049305576913005)
                    ·
                      refine ⟨979207094643489591342377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2611218919049305576913005 979207094643489591342377)
                      ·
                        rfl

theorem cell23_1906999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1906999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1906999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1906999 prefixEnd_1906999 := by exact prefixLift 1906999
  have htrace : WordTrace (prefixWord ++ tailWord_1906999) baseStart_1906999 baseEnd_1906999 := by
    simpa [prefixWord, tailWord_1906999, baseEnd_1906999] using wordTrace_append hprefix tailTrace_1906999
  have hstable : (prefixWord ++ tailWord_1906999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906999).length < 2 ^ (prefixWord ++ tailWord_1906999).sum := by decide
  have hdescent : baseEnd_1906999 < baseStart_1906999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907047 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_1907047 : Nat := 118140960795 + 1907047 * 2 ^ 59
def prefixEnd_1907047 : Nat := 4983230072969 + 3 ^ 40 * 1907047 * 2
def baseEnd_1907047 : Nat := 979231741714905403542157

theorem tailTrace_1907047 : CollatzResearch.WordTrace tailWord_1907047 prefixEnd_1907047 979231741714905403542157 := by
  unfold tailWord_1907047
  simp only [CollatzResearch.WordTrace]
  refine ⟨69555718322101891542591395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46370478881401261028394263 69555718322101891542591395)
  ·
    refine ⟨104333577483152837313887093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69555718322101891542591395 104333577483152837313887093)
    ·
      refine ⟨9781272889045578498176915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104333577483152837313887093 9781272889045578498176915)
      ·
        refine ⟨14671909333568367747265373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9781272889045578498176915 14671909333568367747265373)
        ·
          refine ⟨5501966000088137905224515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14671909333568367747265373 5501966000088137905224515)
          ·
            refine ⟨8252949000132206857836773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501966000088137905224515 8252949000132206857836773)
            ·
              refine ⟨1547427937524788785844395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8252949000132206857836773 1547427937524788785844395)
              ·
                refine ⟨2321141906287183178766593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547427937524788785844395 2321141906287183178766593)
                ·
                  refine ⟨1740856429715387384074945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321141906287183178766593 1740856429715387384074945)
                  ·
                    refine ⟨1305642322286540538056209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1740856429715387384074945 1305642322286540538056209)
                    ·
                      refine ⟨979231741714905403542157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305642322286540538056209 979231741714905403542157)
                      ·
                        rfl

theorem cell23_1907047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_1907047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907047 prefixEnd_1907047 := by exact prefixLift 1907047
  have htrace : WordTrace (prefixWord ++ tailWord_1907047) baseStart_1907047 baseEnd_1907047 := by
    simpa [prefixWord, tailWord_1907047, baseEnd_1907047] using wordTrace_append hprefix tailTrace_1907047
  have hstable : (prefixWord ++ tailWord_1907047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907047).length < 2 ^ (prefixWord ++ tailWord_1907047).sum := by decide
  have hdescent : baseEnd_1907047 < baseStart_1907047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907049 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 4, 5]
def baseStart_1907049 : Nat := 118140960795 + 1907049 * 2 ^ 59
def prefixEnd_1907049 : Nat := 4983230072969 + 3 ^ 40 * 1907049 * 2
def baseEnd_1907049 : Nat := 326410922892071465239049

theorem tailTrace_1907049 : CollatzResearch.WordTrace tailWord_1907049 prefixEnd_1907049 326410922892071465239049 := by
  unfold tailWord_1907049
  simp only [CollatzResearch.WordTrace]
  refine ⟨69555791268094645884164201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46370527512063097256109467 69555791268094645884164201)
  ·
    refine ⟨52166843451070984413123151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69555791268094645884164201 52166843451070984413123151)
    ·
      refine ⟨78250265176606476619684727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52166843451070984413123151 78250265176606476619684727)
      ·
        refine ⟨117375397764909714929527091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78250265176606476619684727 117375397764909714929527091)
        ·
          refine ⟨176063096647364572394290637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117375397764909714929527091 176063096647364572394290637)
          ·
            refine ⟨66023661242761714647858989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176063096647364572394290637 66023661242761714647858989)
            ·
              refine ⟨24758872966035642992947121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66023661242761714647858989 24758872966035642992947121)
              ·
                refine ⟨18569154724526732244710341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24758872966035642992947121 18569154724526732244710341)
                ·
                  refine ⟨3481716510848762295883189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18569154724526732244710341 3481716510848762295883189)
                  ·
                    refine ⟨326410922892071465239049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3481716510848762295883189 326410922892071465239049)
                    ·
                      rfl

theorem cell23_1907049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_1907049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907049 prefixEnd_1907049 := by exact prefixLift 1907049
  have htrace : WordTrace (prefixWord ++ tailWord_1907049) baseStart_1907049 baseEnd_1907049 := by
    simpa [prefixWord, tailWord_1907049, baseEnd_1907049] using wordTrace_append hprefix tailTrace_1907049
  have hstable : (prefixWord ++ tailWord_1907049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907049).length < 2 ^ (prefixWord ++ tailWord_1907049).sum := by decide
  have hdescent : baseEnd_1907049 < baseStart_1907049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907103 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 2, 4, 2]
def baseStart_1907103 : Nat := 118140960795 + 1907103 * 2 ^ 59
def prefixEnd_1907103 : Nat := 4983230072969 + 3 ^ 40 * 1907103 * 2
def baseEnd_1907103 : Nat := 979260496631557184441899

theorem tailTrace_1907103 : CollatzResearch.WordTrace tailWord_1907103 prefixEnd_1907103 979260496631557184441899 := by
  unfold tailWord_1907103
  simp only [CollatzResearch.WordTrace]
  refine ⟨69557760809899013106629963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46371840539932675404419975 69557760809899013106629963)
  ·
    refine ⟨104336641214848519659944945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69557760809899013106629963 104336641214848519659944945)
    ·
      refine ⟨78252480911136389744958709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104336641214848519659944945 78252480911136389744958709)
      ·
        refine ⟨7336170085419036538589879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78252480911136389744958709 7336170085419036538589879)
        ·
          refine ⟨11004255128128554807884819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7336170085419036538589879 11004255128128554807884819)
          ·
            refine ⟨16506382692192832211827229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11004255128128554807884819 16506382692192832211827229)
            ·
              refine ⟨6189893509572312079435211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16506382692192832211827229 6189893509572312079435211)
              ·
                refine ⟨9284840264358468119152817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6189893509572312079435211 9284840264358468119152817)
                ·
                  refine ⟨6963630198268851089364613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9284840264358468119152817 6963630198268851089364613)
                  ·
                    refine ⟨1305680662175409579255865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6963630198268851089364613 1305680662175409579255865)
                    ·
                      refine ⟨979260496631557184441899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305680662175409579255865 979260496631557184441899)
                      ·
                        rfl

theorem cell23_1907103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_1907103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907103 prefixEnd_1907103 := by exact prefixLift 1907103
  have htrace : WordTrace (prefixWord ++ tailWord_1907103) baseStart_1907103 baseEnd_1907103 := by
    simpa [prefixWord, tailWord_1907103, baseEnd_1907103] using wordTrace_append hprefix tailTrace_1907103
  have hstable : (prefixWord ++ tailWord_1907103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907103).length < 2 ^ (prefixWord ++ tailWord_1907103).sum := by decide
  have hdescent : baseEnd_1907103 < baseStart_1907103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907117 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1907117 : Nat := 118140960795 + 1907117 * 2 ^ 59
def prefixEnd_1907117 : Nat := 4983230072969 + 3 ^ 40 * 1907117 * 2
def baseEnd_1907117 : Nat := 326422561786906709888945

theorem tailTrace_1907117 : CollatzResearch.WordTrace tailWord_1907117 prefixEnd_1907117 326422561786906709888945 := by
  unfold tailWord_1907117
  simp only [CollatzResearch.WordTrace]
  refine ⟨69558271431848293497639605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46372180954565528998426403 69558271431848293497639605)
  ·
    refine ⟨6521087946735777515403713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69558271431848293497639605 6521087946735777515403713)
    ·
      refine ⟨4890815960051833136552785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6521087946735777515403713 4890815960051833136552785)
      ·
        refine ⟨3668111970038874852414589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4890815960051833136552785 3668111970038874852414589)
        ·
          refine ⟨1375541988764578069655471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3668111970038874852414589 1375541988764578069655471)
          ·
            refine ⟨2063312983146867104483207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375541988764578069655471 2063312983146867104483207)
            ·
              refine ⟨3094969474720300656724811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063312983146867104483207 3094969474720300656724811)
              ·
                refine ⟨4642454212080450985087217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094969474720300656724811 4642454212080450985087217)
                ·
                  refine ⟨3481840659060338238815413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642454212080450985087217 3481840659060338238815413)
                  ·
                    refine ⟨326422561786906709888945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3481840659060338238815413 326422561786906709888945)
                    ·
                      rfl

theorem cell23_1907117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1907117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907117 prefixEnd_1907117 := by exact prefixLift 1907117
  have htrace : WordTrace (prefixWord ++ tailWord_1907117) baseStart_1907117 baseEnd_1907117 := by
    simpa [prefixWord, tailWord_1907117, baseEnd_1907117] using wordTrace_append hprefix tailTrace_1907117
  have hstable : (prefixWord ++ tailWord_1907117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907117).length < 2 ^ (prefixWord ++ tailWord_1907117).sum := by decide
  have hdescent : baseEnd_1907117 < baseStart_1907117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907143 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 6]
def baseStart_1907143 : Nat := 118140960795 + 1907143 * 2 ^ 59
def prefixEnd_1907143 : Nat := 4983230072969 + 3 ^ 40 * 1907143 * 2
def baseEnd_1907143 : Nat := 108809003984193003104635

theorem tailTrace_1907143 : CollatzResearch.WordTrace tailWord_1907143 prefixEnd_1907143 108809003984193003104635 := by
  unfold tailWord_1907143
  simp only [CollatzResearch.WordTrace]
  refine ⟨69559219729754099938086083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46372813153169399958724055 69559219729754099938086083)
  ·
    refine ⟨104338829594631149907129125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69559219729754099938086083 104338829594631149907129125)
    ·
      refine ⟨19563530548993340607586711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104338829594631149907129125 19563530548993340607586711)
      ·
        refine ⟨29345295823490010911380067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19563530548993340607586711 29345295823490010911380067)
        ·
          refine ⟨44017943735235016367070101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29345295823490010911380067 44017943735235016367070101)
          ·
            refine ⟨2063341112589141392206411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44017943735235016367070101 2063341112589141392206411)
            ·
              refine ⟨3095011668883712088309617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063341112589141392206411 3095011668883712088309617)
              ·
                refine ⟨2321258751662784066232213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095011668883712088309617 2321258751662784066232213)
                ·
                  refine ⟨108809003984193003104635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2321258751662784066232213 108809003984193003104635)
                  ·
                    rfl

theorem cell23_1907143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 6].length) (baseStart_1907143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907143 prefixEnd_1907143 := by exact prefixLift 1907143
  have htrace : WordTrace (prefixWord ++ tailWord_1907143) baseStart_1907143 baseEnd_1907143 := by
    simpa [prefixWord, tailWord_1907143, baseEnd_1907143] using wordTrace_append hprefix tailTrace_1907143
  have hstable : (prefixWord ++ tailWord_1907143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907143).length < 2 ^ (prefixWord ++ tailWord_1907143).sum := by decide
  have hdescent : baseEnd_1907143 < baseStart_1907143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907193 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 4]
def baseStart_1907193 : Nat := 118140960795 + 1907193 * 2 ^ 59
def prefixEnd_1907193 : Nat := 4983230072969 + 3 ^ 40 * 1907193 * 2
def baseEnd_1907193 : Nat := 979306709890461832316485

theorem tailTrace_1907193 : CollatzResearch.WordTrace tailWord_1907193 prefixEnd_1907193 979306709890461832316485 := by
  unfold tailWord_1907193
  simp only [CollatzResearch.WordTrace]
  refine ⟨69561043379572958477406233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46374028919715305651604155 69561043379572958477406233)
  ·
    refine ⟨52170782534679718858054675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69561043379572958477406233 52170782534679718858054675)
    ·
      refine ⟨78256173802019578287082013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52170782534679718858054675 78256173802019578287082013)
      ·
        refine ⟨29346065175757341857655755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78256173802019578287082013 29346065175757341857655755)
        ·
          refine ⟨44019097763636012786483633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29346065175757341857655755 44019097763636012786483633)
          ·
            refine ⟨33014323322727009589862725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44019097763636012786483633 33014323322727009589862725)
            ·
              refine ⟨6190185623011314298099261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33014323322727009589862725 6190185623011314298099261)
              ·
                refine ⟨2321319608629242861787223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6190185623011314298099261 2321319608629242861787223)
                ·
                  refine ⟨3481979412943864292680835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321319608629242861787223 3481979412943864292680835)
                  ·
                    refine ⟨5222969119415796439021253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3481979412943864292680835 5222969119415796439021253)
                    ·
                      refine ⟨979306709890461832316485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5222969119415796439021253 979306709890461832316485)
                      ·
                        rfl

theorem cell23_1907193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_1907193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907193 prefixEnd_1907193 := by exact prefixLift 1907193
  have htrace : WordTrace (prefixWord ++ tailWord_1907193) baseStart_1907193 baseEnd_1907193 := by
    simpa [prefixWord, tailWord_1907193, baseEnd_1907193] using wordTrace_append hprefix tailTrace_1907193
  have hstable : (prefixWord ++ tailWord_1907193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907193).length < 2 ^ (prefixWord ++ tailWord_1907193).sum := by decide
  have hdescent : baseEnd_1907193 < baseStart_1907193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907203 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 2, 4]
def baseStart_1907203 : Nat := 118140960795 + 1907203 * 2 ^ 59
def prefixEnd_1907203 : Nat := 4983230072969 + 3 ^ 40 * 1907203 * 2
def baseEnd_1907203 : Nat := 326437281565668931063813

theorem tailTrace_1907203 : CollatzResearch.WordTrace tailWord_1907203 prefixEnd_1907203 326437281565668931063813 := by
  unfold tailWord_1907203
  simp only [CollatzResearch.WordTrace]
  refine ⟨69561408109536730185270263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46374272073024486790180175 69561408109536730185270263)
  ·
    refine ⟨104342112164305095277905395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69561408109536730185270263 104342112164305095277905395)
    ·
      refine ⟨156513168246457642916858093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104342112164305095277905395 156513168246457642916858093)
      ·
        refine ⟨58692438092421616093821785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156513168246457642916858093 58692438092421616093821785)
        ·
          refine ⟨44019328569316212070366339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58692438092421616093821785 44019328569316212070366339)
          ·
            refine ⟨66028992853974318105549509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44019328569316212070366339 66028992853974318105549509)
            ·
              refine ⟨12380436160120184644790533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66028992853974318105549509 12380436160120184644790533)
              ·
                refine ⟨2321331780022534620898225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12380436160120184644790533 2321331780022534620898225)
                ·
                  refine ⟨1740998835016900965673669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321331780022534620898225 1740998835016900965673669)
                  ·
                    refine ⟨326437281565668931063813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1740998835016900965673669 326437281565668931063813)
                    ·
                      rfl

theorem cell23_1907203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 4].length) (baseStart_1907203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907203 prefixEnd_1907203 := by exact prefixLift 1907203
  have htrace : WordTrace (prefixWord ++ tailWord_1907203) baseStart_1907203 baseEnd_1907203 := by
    simpa [prefixWord, tailWord_1907203, baseEnd_1907203] using wordTrace_append hprefix tailTrace_1907203
  have hstable : (prefixWord ++ tailWord_1907203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907203).length < 2 ^ (prefixWord ++ tailWord_1907203).sum := by decide
  have hdescent : baseEnd_1907203 < baseStart_1907203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907240 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1907240 : Nat := 118140960795 + 1907240 * 2 ^ 59
def prefixEnd_1907240 : Nat := 4983230072969 + 3 ^ 40 * 1907240 * 2
def baseEnd_1907240 : Nat := 979330843481223148428769

theorem tailTrace_1907240 : CollatzResearch.WordTrace tailWord_1907240 prefixEnd_1907240 979330843481223148428769 := by
  unfold tailWord_1907240
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781378805201342752183587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46375171740268457002911449 34781378805201342752183587)
  ·
    refine ⟨52172068207802014128275381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34781378805201342752183587 52172068207802014128275381)
    ·
      refine ⟨4891131394481438824525817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52172068207802014128275381 4891131394481438824525817)
      ·
        refine ⟨3668348545861079118394363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4891131394481438824525817 3668348545861079118394363)
        ·
          refine ⟨5502522818791618677591545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668348545861079118394363 5502522818791618677591545)
          ·
            refine ⟨4126892114093714008193659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5502522818791618677591545 4126892114093714008193659)
            ·
              refine ⟨6190338171140571012290489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126892114093714008193659 6190338171140571012290489)
              ·
                refine ⟨4642753628355428259217867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6190338171140571012290489 4642753628355428259217867)
                ·
                  refine ⟨6964130442533142388826801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642753628355428259217867 6964130442533142388826801)
                  ·
                    refine ⟨5223097831899856791620101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6964130442533142388826801 5223097831899856791620101)
                    ·
                      refine ⟨979330843481223148428769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5223097831899856791620101 979330843481223148428769)
                      ·
                        rfl

theorem cell23_1907240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1907240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907240 prefixEnd_1907240 := by exact prefixLift 1907240
  have htrace : WordTrace (prefixWord ++ tailWord_1907240) baseStart_1907240 baseEnd_1907240 := by
    simpa [prefixWord, tailWord_1907240, baseEnd_1907240] using wordTrace_append hprefix tailTrace_1907240
  have hstable : (prefixWord ++ tailWord_1907240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907240).length < 2 ^ (prefixWord ++ tailWord_1907240).sum := by decide
  have hdescent : baseEnd_1907240 < baseStart_1907240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907243 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 3]
def baseStart_1907243 : Nat := 118140960795 + 1907243 * 2 ^ 59
def prefixEnd_1907243 : Nat := 4983230072969 + 3 ^ 40 * 1907243 * 2
def baseEnd_1907243 : Nat := 979332383923186636691255

theorem tailTrace_1907243 : CollatzResearch.WordTrace tailWord_1907243 prefixEnd_1907243 979332383923186636691255 := by
  unfold tailWord_1907243
  simp only [CollatzResearch.WordTrace]
  refine ⟨69562867029391817016726383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46375244686261211344484255 69562867029391817016726383)
  ·
    refine ⟨104344300544087725525089575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69562867029391817016726383 104344300544087725525089575)
    ·
      refine ⟨156516450816131588287634363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104344300544087725525089575 156516450816131588287634363)
      ·
        refine ⟨234774676224197382431451545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156516450816131588287634363 234774676224197382431451545)
        ·
          refine ⟨176081007168148036823588659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234774676224197382431451545 176081007168148036823588659)
          ·
            refine ⟨264121510752222055235382989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176081007168148036823588659 264121510752222055235382989)
            ·
              refine ⟨99045566532083270713268621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264121510752222055235382989 99045566532083270713268621)
              ·
                refine ⟨37142087449531226517475733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99045566532083270713268621 37142087449531226517475733)
                ·
                  refine ⟨1741035349196776243006675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37142087449531226517475733 1741035349196776243006675)
                  ·
                    refine ⟨2611553023795164364510013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741035349196776243006675 2611553023795164364510013)
                    ·
                      refine ⟨979332383923186636691255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2611553023795164364510013 979332383923186636691255)
                      ·
                        rfl

theorem cell23_1907243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 3].length) (baseStart_1907243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907243 prefixEnd_1907243 := by exact prefixLift 1907243
  have htrace : WordTrace (prefixWord ++ tailWord_1907243) baseStart_1907243 baseEnd_1907243 := by
    simpa [prefixWord, tailWord_1907243, baseEnd_1907243] using wordTrace_append hprefix tailTrace_1907243
  have hstable : (prefixWord ++ tailWord_1907243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907243).length < 2 ^ (prefixWord ++ tailWord_1907243).sum := by decide
  have hdescent : baseEnd_1907243 < baseStart_1907243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907261 : List Nat := [1, 4, 1, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_1907261 : Nat := 118140960795 + 1907261 * 2 ^ 59
def prefixEnd_1907261 : Nat := 4983230072969 + 3 ^ 40 * 1907261 * 2
def baseEnd_1907261 : Nat := 979341626574967566266173

theorem tailTrace_1907261 : CollatzResearch.WordTrace tailWord_1907261 prefixEnd_1907261 979341626574967566266173 := by
  unfold tailWord_1907261
  simp only [CollatzResearch.WordTrace]
  refine ⟨69563523543326606090881637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46375682362217737393921091 69563523543326606090881637)
  ·
    refine ⟨13043160664373738642040307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69563523543326606090881637 13043160664373738642040307)
    ·
      refine ⟨19564740996560607963060461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13043160664373738642040307 19564740996560607963060461)
      ·
        refine ⟨7336777873710227986147673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19564740996560607963060461 7336777873710227986147673)
        ·
          refine ⟨5502583405282670989610755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7336777873710227986147673 5502583405282670989610755)
          ·
            refine ⟨8253875107924006484416133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502583405282670989610755 8253875107924006484416133)
            ·
              refine ⟨1547601582735751215828025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8253875107924006484416133 1547601582735751215828025)
              ·
                refine ⟨1160701187051813411871019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547601582735751215828025 1160701187051813411871019)
                ·
                  refine ⟨1741051780577720117806529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160701187051813411871019 1741051780577720117806529)
                  ·
                    refine ⟨1305788835433290088354897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1741051780577720117806529 1305788835433290088354897)
                    ·
                      refine ⟨979341626574967566266173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305788835433290088354897 979341626574967566266173)
                      ·
                        rfl

theorem cell23_1907261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_1907261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907261 prefixEnd_1907261 := by exact prefixLift 1907261
  have htrace : WordTrace (prefixWord ++ tailWord_1907261) baseStart_1907261 baseEnd_1907261 := by
    simpa [prefixWord, tailWord_1907261, baseEnd_1907261] using wordTrace_append hprefix tailTrace_1907261
  have hstable : (prefixWord ++ tailWord_1907261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907261).length < 2 ^ (prefixWord ++ tailWord_1907261).sum := by decide
  have hdescent : baseEnd_1907261 < baseStart_1907261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907277 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1907277 : Nat := 118140960795 + 1907277 * 2 ^ 59
def prefixEnd_1907277 : Nat := 4983230072969 + 3 ^ 40 * 1907277 * 2
def baseEnd_1907277 : Nat := 979349842265439503666099

theorem tailTrace_1907277 : CollatzResearch.WordTrace tailWord_1907277 prefixEnd_1907277 979349842265439503666099 := by
  unfold tailWord_1907277
  simp only [CollatzResearch.WordTrace]
  refine ⟨69564107111268640823464085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46376071407512427215642723 69564107111268640823464085)
  ·
    refine ⟨3260817520840717538599879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69564107111268640823464085 3260817520840717538599879)
    ·
      refine ⟨4891226281261076307899819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3260817520840717538599879 4891226281261076307899819)
      ·
        refine ⟨7336839421891614461849729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4891226281261076307899819 7336839421891614461849729)
        ·
          refine ⟨5502629566418710846387297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7336839421891614461849729 5502629566418710846387297)
          ·
            refine ⟨4126972174814033134790473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5502629566418710846387297 4126972174814033134790473)
            ·
              refine ⟨3095229131110524851092855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126972174814033134790473 3095229131110524851092855)
              ·
                refine ⟨4642843696665787276639283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095229131110524851092855 4642843696665787276639283)
                ·
                  refine ⟨6964265544998680914958925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642843696665787276639283 6964265544998680914958925)
                  ·
                    refine ⟨2611599579374505343109597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6964265544998680914958925 2611599579374505343109597)
                    ·
                      refine ⟨979349842265439503666099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2611599579374505343109597 979349842265439503666099)
                      ·
                        rfl

theorem cell23_1907277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1907277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907277 prefixEnd_1907277 := by exact prefixLift 1907277
  have htrace : WordTrace (prefixWord ++ tailWord_1907277) baseStart_1907277 baseEnd_1907277 := by
    simpa [prefixWord, tailWord_1907277, baseEnd_1907277] using wordTrace_append hprefix tailTrace_1907277
  have hstable : (prefixWord ++ tailWord_1907277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907277).length < 2 ^ (prefixWord ++ tailWord_1907277).sum := by decide
  have hdescent : baseEnd_1907277 < baseStart_1907277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907298 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1907298 : Nat := 118140960795 + 1907298 * 2 ^ 59
def prefixEnd_1907298 : Nat := 4983230072969 + 3 ^ 40 * 1907298 * 2
def baseEnd_1907298 : Nat := 979360625359183921503503

theorem tailTrace_1907298 : CollatzResearch.WordTrace tailWord_1907298 prefixEnd_1907298 979360625359183921503503 := by
  unfold tailWord_1907298
  simp only [CollatzResearch.WordTrace]
  refine ⟨17391218261048140352494637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46376582029461707606652365 17391218261048140352494637)
  ·
    refine ⟨6521706847893052632185489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17391218261048140352494637 6521706847893052632185489)
    ·
      refine ⟨4891280135919789474139117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6521706847893052632185489 4891280135919789474139117)
      ·
        refine ⟨1834230050969921052802169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4891280135919789474139117 1834230050969921052802169)
        ·
          refine ⟨1375672538227440789601627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1834230050969921052802169 1375672538227440789601627)
          ·
            refine ⟨2063508807341161184402441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375672538227440789601627 2063508807341161184402441)
            ·
              refine ⟨1547631605505870888301831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063508807341161184402441 1547631605505870888301831)
              ·
                refine ⟨2321447408258806332452747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547631605505870888301831 2321447408258806332452747)
                ·
                  refine ⟨3482171112388209498679121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321447408258806332452747 3482171112388209498679121)
                  ·
                    refine ⟨2611628334291157124009341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3482171112388209498679121 2611628334291157124009341)
                    ·
                      refine ⟨979360625359183921503503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2611628334291157124009341 979360625359183921503503)
                      ·
                        rfl

theorem cell23_1907298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1907298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907298 prefixEnd_1907298 := by exact prefixLift 1907298
  have htrace : WordTrace (prefixWord ++ tailWord_1907298) baseStart_1907298 baseEnd_1907298 := by
    simpa [prefixWord, tailWord_1907298, baseEnd_1907298] using wordTrace_append hprefix tailTrace_1907298
  have hstable : (prefixWord ++ tailWord_1907298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907298).length < 2 ^ (prefixWord ++ tailWord_1907298).sum := by decide
  have hdescent : baseEnd_1907298 < baseStart_1907298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907300 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_1907300 : Nat := 118140960795 + 1907300 * 2 ^ 59
def prefixEnd_1907300 : Nat := 4983230072969 + 3 ^ 40 * 1907300 * 2
def baseEnd_1907300 : Nat := 979361652320492913678493

theorem tailTrace_1907300 : CollatzResearch.WordTrace tailWord_1907300 prefixEnd_1907300 979361652320492913678493 := by
  unfold tailWord_1907300
  simp only [CollatzResearch.WordTrace]
  refine ⟨34782472995092657875775677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46376630660123543834367569 34782472995092657875775677)
  ·
    refine ⟨13043427373159746703415879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34782472995092657875775677 13043427373159746703415879)
    ·
      refine ⟨19565141059739620055123819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13043427373159746703415879 19565141059739620055123819)
      ·
        refine ⟨29347711589609430082685729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19565141059739620055123819 29347711589609430082685729)
        ·
          refine ⟨22010783692207072562014297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29347711589609430082685729 22010783692207072562014297)
          ·
            refine ⟨16508087769155304421510723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22010783692207072562014297 16508087769155304421510723)
            ·
              refine ⟨24762131653732956632266085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16508087769155304421510723 24762131653732956632266085)
              ·
                refine ⟨4642899685074929368549891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24762131653732956632266085 4642899685074929368549891)
                ·
                  refine ⟨6964349527612394052824837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642899685074929368549891 6964349527612394052824837)
                  ·
                    refine ⟨1305815536427323884904657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6964349527612394052824837 1305815536427323884904657)
                    ·
                      refine ⟨979361652320492913678493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305815536427323884904657 979361652320492913678493)
                      ·
                        rfl

theorem cell23_1907300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_1907300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907300 prefixEnd_1907300 := by exact prefixLift 1907300
  have htrace : WordTrace (prefixWord ++ tailWord_1907300) baseStart_1907300 baseEnd_1907300 := by
    simpa [prefixWord, tailWord_1907300, baseEnd_1907300] using wordTrace_append hprefix tailTrace_1907300
  have hstable : (prefixWord ++ tailWord_1907300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907300).length < 2 ^ (prefixWord ++ tailWord_1907300).sum := by decide
  have hdescent : baseEnd_1907300 < baseStart_1907300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907304 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1907304 : Nat := 118140960795 + 1907304 * 2 ^ 59
def prefixEnd_1907304 : Nat := 4983230072969 + 3 ^ 40 * 1907304 * 2
def baseEnd_1907304 : Nat := 979363706243110898028475

theorem tailTrace_1907304 : CollatzResearch.WordTrace tailWord_1907304 prefixEnd_1907304 979363706243110898028475 := by
  unfold tailWord_1907304
  simp only [CollatzResearch.WordTrace]
  refine ⟨34782545941085412217348483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46376727921447216289797977 34782545941085412217348483)
  ·
    refine ⟨52173818911628118326022725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34782545941085412217348483 52173818911628118326022725)
    ·
      refine ⟨9782591045930272186129261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52173818911628118326022725 9782591045930272186129261)
      ·
        refine ⟨3668471642223852069798473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9782591045930272186129261 3668471642223852069798473)
        ·
          refine ⟨2751353731667889052348855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3668471642223852069798473 2751353731667889052348855)
          ·
            refine ⟨4127030597501833578523283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751353731667889052348855 4127030597501833578523283)
            ·
              refine ⟨6190545896252750367784925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127030597501833578523283 6190545896252750367784925)
              ·
                refine ⟨2321454711094781387919347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6190545896252750367784925 2321454711094781387919347)
                ·
                  refine ⟨3482182066642172081879021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321454711094781387919347 3482182066642172081879021)
                  ·
                    refine ⟨1305818274990814530704633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482182066642172081879021 1305818274990814530704633)
                    ·
                      refine ⟨979363706243110898028475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305818274990814530704633 979363706243110898028475)
                      ·
                        rfl

theorem cell23_1907304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1907304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907304 prefixEnd_1907304 := by exact prefixLift 1907304
  have htrace : WordTrace (prefixWord ++ tailWord_1907304) baseStart_1907304 baseEnd_1907304 := by
    simpa [prefixWord, tailWord_1907304, baseEnd_1907304] using wordTrace_append hprefix tailTrace_1907304
  have hstable : (prefixWord ++ tailWord_1907304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907304).length < 2 ^ (prefixWord ++ tailWord_1907304).sum := by decide
  have hdescent : baseEnd_1907304 < baseStart_1907304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907353 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 2, 5]
def baseStart_1907353 : Nat := 118140960795 + 1907353 * 2 ^ 59
def prefixEnd_1907353 : Nat := 4983230072969 + 3 ^ 40 * 1907353 * 2
def baseEnd_1907353 : Nat := 326462955598393735438583

theorem tailTrace_1907353 : CollatzResearch.WordTrace tailWord_1907353 prefixEnd_1907353 326462955598393735438583 := by
  unfold tailWord_1907353
  simp only [CollatzResearch.WordTrace]
  refine ⟨69566879058993305803230713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46377919372662203868820475 69566879058993305803230713)
  ·
    refine ⟨52175159294244979352423035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69566879058993305803230713 52175159294244979352423035)
    ·
      refine ⟨78262738941367469028634553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52175159294244979352423035 78262738941367469028634553)
      ·
        refine ⟨58697054206025601771475915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78262738941367469028634553 58697054206025601771475915)
        ·
          refine ⟨88045581309038402657213873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58697054206025601771475915 88045581309038402657213873)
          ·
            refine ⟨66034185981778801992910405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88045581309038402657213873 66034185981778801992910405)
            ·
              refine ⟨12381409871583525373670701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66034185981778801992910405 12381409871583525373670701)
              ·
                refine ⟨4643028701843822015126513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12381409871583525373670701 4643028701843822015126513)
                ·
                  refine ⟨3482271526382866511344885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643028701843822015126513 3482271526382866511344885)
                  ·
                    refine ⟨326462955598393735438583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3482271526382866511344885 326462955598393735438583)
                    ·
                      rfl

theorem cell23_1907353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_1907353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907353 prefixEnd_1907353 := by exact prefixLift 1907353
  have htrace : WordTrace (prefixWord ++ tailWord_1907353) baseStart_1907353 baseEnd_1907353 := by
    simpa [prefixWord, tailWord_1907353, baseEnd_1907353] using wordTrace_append hprefix tailTrace_1907353
  have hstable : (prefixWord ++ tailWord_1907353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907353).length < 2 ^ (prefixWord ++ tailWord_1907353).sum := by decide
  have hdescent : baseEnd_1907353 < baseStart_1907353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907390 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1907390 : Nat := 118140960795 + 1907390 * 2 ^ 59
def prefixEnd_1907390 : Nat := 4983230072969 + 3 ^ 40 * 1907390 * 2
def baseEnd_1907390 : Nat := 979407865579397561553079

theorem tailTrace_1907390 : CollatzResearch.WordTrace tailWord_1907390 prefixEnd_1907390 979407865579397561553079 := by
  unfold tailWord_1907390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696028569982407640290953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46378819039906174081551749 8696028569982407640290953)
  ·
    refine ⟨6522021427486805730218215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8696028569982407640290953 6522021427486805730218215)
    ·
      refine ⟨9783032141230208595327323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6522021427486805730218215 9783032141230208595327323)
      ·
        refine ⟨14674548211845312892990985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9783032141230208595327323 14674548211845312892990985)
        ·
          refine ⟨11005911158883984669743239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14674548211845312892990985 11005911158883984669743239)
          ·
            refine ⟨16508866738325977004614859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005911158883984669743239 16508866738325977004614859)
            ·
              refine ⟨24763300107488965506922289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16508866738325977004614859 24763300107488965506922289)
              ·
                refine ⟨18572475080616724130191717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24763300107488965506922289 18572475080616724130191717)
                ·
                  refine ⟨3482339077615635774410947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18572475080616724130191717 3482339077615635774410947)
                  ·
                    refine ⟨5223508616423453661616421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3482339077615635774410947 5223508616423453661616421)
                    ·
                      refine ⟨979407865579397561553079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5223508616423453661616421 979407865579397561553079)
                      ·
                        rfl

theorem cell23_1907390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1907390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907390 prefixEnd_1907390 := by exact prefixLift 1907390
  have htrace : WordTrace (prefixWord ++ tailWord_1907390) baseStart_1907390 baseEnd_1907390 := by
    simpa [prefixWord, tailWord_1907390, baseEnd_1907390] using wordTrace_append hprefix tailTrace_1907390
  have hstable : (prefixWord ++ tailWord_1907390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907390).length < 2 ^ (prefixWord ++ tailWord_1907390).sum := by decide
  have hdescent : baseEnd_1907390 < baseStart_1907390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907417 : List Nat := [1, 2, 1, 2, 3, 2, 2, 5, 1, 4]
def baseStart_1907417 : Nat := 118140960795 + 1907417 * 2 ^ 59
def prefixEnd_1907417 : Nat := 4983230072969 + 3 ^ 40 * 1907417 * 2
def baseEnd_1907417 : Nat := 326473909852356318638485

theorem tailTrace_1907417 : CollatzResearch.WordTrace tailWord_1907417 prefixEnd_1907417 326473909852356318638485 := by
  unfold tailWord_1907417
  simp only [CollatzResearch.WordTrace]
  refine ⟨69569213330761444733560505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46379475553840963155707003 69569213330761444733560505)
  ·
    refine ⟨52176909998071083550170379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69569213330761444733560505 52176909998071083550170379)
    ·
      refine ⟨78265364997106625325255569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52176909998071083550170379 78265364997106625325255569)
      ·
        refine ⟨58699023747829968993941677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78265364997106625325255569 58699023747829968993941677)
        ·
          refine ⟨22012133905436238372728129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58699023747829968993941677 22012133905436238372728129)
          ·
            refine ⟨16509100429077178779546097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22012133905436238372728129 16509100429077178779546097)
            ·
              refine ⟨12381825321807884084659573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16509100429077178779546097 12381825321807884084659573)
              ·
                refine ⟨1160796123919489132936835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12381825321807884084659573 1160796123919489132936835)
                ·
                  refine ⟨1741194185879233699405253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160796123919489132936835 1741194185879233699405253)
                  ·
                    refine ⟨326473909852356318638485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1741194185879233699405253 326473909852356318638485)
                    ·
                      rfl

theorem cell23_1907417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 4].length) (baseStart_1907417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907417 prefixEnd_1907417 := by exact prefixLift 1907417
  have htrace : WordTrace (prefixWord ++ tailWord_1907417) baseStart_1907417 baseEnd_1907417 := by
    simpa [prefixWord, tailWord_1907417, baseEnd_1907417] using wordTrace_append hprefix tailTrace_1907417
  have hstable : (prefixWord ++ tailWord_1907417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907417).length < 2 ^ (prefixWord ++ tailWord_1907417).sum := by decide
  have hdescent : baseEnd_1907417 < baseStart_1907417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907427 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1907427 : Nat := 118140960795 + 1907427 * 2 ^ 59
def prefixEnd_1907427 : Nat := 4983230072969 + 3 ^ 40 * 1907427 * 2
def baseEnd_1907427 : Nat := 979426864363613916790409

theorem tailTrace_1907427 : CollatzResearch.WordTrace tailWord_1907427 prefixEnd_1907427 979426864363613916790409 := by
  unfold tailWord_1907427
  simp only [CollatzResearch.WordTrace]
  refine ⟨69569578060725216441424535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46379718707150144294283023 69569578060725216441424535)
  ·
    refine ⟨104354367091087824662136803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69569578060725216441424535 104354367091087824662136803)
    ·
      refine ⟨156531550636631736993205205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104354367091087824662136803 156531550636631736993205205)
      ·
        refine ⟨3668708218046056335778247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 156531550636631736993205205 3668708218046056335778247)
        ·
          refine ⟨5503062327069084503667371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668708218046056335778247 5503062327069084503667371)
          ·
            refine ⟨8254593490603626755501057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503062327069084503667371 8254593490603626755501057)
            ·
              refine ⟨6190945117952720066625793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8254593490603626755501057 6190945117952720066625793)
              ·
                refine ⟨4643208838464540049969345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6190945117952720066625793 4643208838464540049969345)
                ·
                  refine ⟨3482406628848405037477009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643208838464540049969345 3482406628848405037477009)
                  ·
                    refine ⟨2611804971636303778107757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3482406628848405037477009 2611804971636303778107757)
                    ·
                      refine ⟨979426864363613916790409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2611804971636303778107757 979426864363613916790409)
                      ·
                        rfl

theorem cell23_1907427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1907427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907427 prefixEnd_1907427 := by exact prefixLift 1907427
  have htrace : WordTrace (prefixWord ++ tailWord_1907427) baseStart_1907427 baseEnd_1907427 := by
    simpa [prefixWord, tailWord_1907427, baseEnd_1907427] using wordTrace_append hprefix tailTrace_1907427
  have hstable : (prefixWord ++ tailWord_1907427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907427).length < 2 ^ (prefixWord ++ tailWord_1907427).sum := by decide
  have hdescent : baseEnd_1907427 < baseStart_1907427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907453 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_1907453 : Nat := 118140960795 + 1907453 * 2 ^ 59
def prefixEnd_1907453 : Nat := 4983230072969 + 3 ^ 40 * 1907453 * 2
def baseEnd_1907453 : Nat := 979440214860630815065289

theorem tailTrace_1907453 : CollatzResearch.WordTrace tailWord_1907453 prefixEnd_1907453 979440214860630815065289 := by
  unfold tailWord_1907453
  simp only [CollatzResearch.WordTrace]
  refine ⟨69570526358631022881871013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46380350905754015254580675 69570526358631022881871013)
  ·
    refine ⟨13044473692243316790350815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69570526358631022881871013 13044473692243316790350815)
    ·
      refine ⟨19566710538364975185526223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13044473692243316790350815 19566710538364975185526223)
      ·
        refine ⟨29350065807547462778289335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19566710538364975185526223 29350065807547462778289335)
        ·
          refine ⟨44025098711321194167434003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29350065807547462778289335 44025098711321194167434003)
          ·
            refine ⟨66037648066981791251151005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44025098711321194167434003 66037648066981791251151005)
            ·
              refine ⟨24764118025118171719181627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66037648066981791251151005 24764118025118171719181627)
              ·
                refine ⟨37146177037677257578772441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24764118025118171719181627 37146177037677257578772441)
                ·
                  refine ⟨27859632778257943184079331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37146177037677257578772441 27859632778257943184079331)
                  ·
                    refine ⟨41789449167386914776118997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27859632778257943184079331 41789449167386914776118997)
                    ·
                      refine ⟨979440214860630815065289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41789449167386914776118997 979440214860630815065289)
                      ·
                        rfl

theorem cell23_1907453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_1907453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907453 prefixEnd_1907453 := by exact prefixLift 1907453
  have htrace : WordTrace (prefixWord ++ tailWord_1907453) baseStart_1907453 baseEnd_1907453 := by
    simpa [prefixWord, tailWord_1907453, baseEnd_1907453] using wordTrace_append hprefix tailTrace_1907453
  have hstable : (prefixWord ++ tailWord_1907453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907453).length < 2 ^ (prefixWord ++ tailWord_1907453).sum := by decide
  have hdescent : baseEnd_1907453 < baseStart_1907453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907460 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1907460 : Nat := 118140960795 + 1907460 * 2 ^ 59
def prefixEnd_1907460 : Nat := 4983230072969 + 3 ^ 40 * 1907460 * 2
def baseEnd_1907460 : Nat := 326481269741737429225919

theorem tailTrace_1907460 : CollatzResearch.WordTrace tailWord_1907460 prefixEnd_1907460 326481269741737429225919 := by
  unfold tailWord_1907460
  simp only [CollatzResearch.WordTrace]
  refine ⟨34785390834802831538687917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46380521113070442051583889 34785390834802831538687917)
  ·
    refine ⟨13044521563051061827007969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34785390834802831538687917 13044521563051061827007969)
    ·
      refine ⟨9783391172288296370255977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13044521563051061827007969 9783391172288296370255977)
      ·
        refine ⟨7337543379216222277691983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9783391172288296370255977 7337543379216222277691983)
        ·
          refine ⟨11006315068824333416537975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337543379216222277691983 11006315068824333416537975)
          ·
            refine ⟨16509472603236500124806963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006315068824333416537975 16509472603236500124806963)
            ·
              refine ⟨24764208904854750187210445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16509472603236500124806963 24764208904854750187210445)
              ·
                refine ⟨9286578339320531320203917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24764208904854750187210445 9286578339320531320203917)
                ·
                  refine ⟨3482466877245199245076469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9286578339320531320203917 3482466877245199245076469)
                  ·
                    refine ⟨326481269741737429225919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3482466877245199245076469 326481269741737429225919)
                    ·
                      rfl

theorem cell23_1907460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1907460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907460 prefixEnd_1907460 := by exact prefixLift 1907460
  have htrace : WordTrace (prefixWord ++ tailWord_1907460) baseStart_1907460 baseEnd_1907460 := by
    simpa [prefixWord, tailWord_1907460, baseEnd_1907460] using wordTrace_append hprefix tailTrace_1907460
  have hstable : (prefixWord ++ tailWord_1907460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907460).length < 2 ^ (prefixWord ++ tailWord_1907460).sum := by decide
  have hdescent : baseEnd_1907460 < baseStart_1907460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907497 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 7, 2, 2]
def baseStart_1907497 : Nat := 118140960795 + 1907497 * 2 ^ 59
def prefixEnd_1907497 : Nat := 4983230072969 + 3 ^ 40 * 1907497 * 2
def baseEnd_1907497 : Nat := 979462808009428642915087

theorem tailTrace_1907497 : CollatzResearch.WordTrace tailWord_1907497 prefixEnd_1907497 979462808009428642915087 := by
  unfold tailWord_1907497
  simp only [CollatzResearch.WordTrace]
  refine ⟨69572131170471618396472745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46381420780314412264315163 69572131170471618396472745)
  ·
    refine ⟨52179098377853713797354559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69572131170471618396472745 52179098377853713797354559)
    ·
      refine ⟨78268647566780570696031839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52179098377853713797354559 78268647566780570696031839)
      ·
        refine ⟨117402971350170856044047759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78268647566780570696031839 117402971350170856044047759)
        ·
          refine ⟨176104457025256284066071639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117402971350170856044047759 176104457025256284066071639)
          ·
            refine ⟨264156685537884426099107459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176104457025256284066071639 264156685537884426099107459)
            ·
              refine ⟨396235028306826639148661189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264156685537884426099107459 396235028306826639148661189)
              ·
                refine ⟨74294067807529994840373973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396235028306826639148661189 74294067807529994840373973)
                ·
                  refine ⟨1741267214238984254071265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74294067807529994840373973 1741267214238984254071265)
                  ·
                    refine ⟨1305950410679238190553449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1741267214238984254071265 1305950410679238190553449)
                    ·
                      refine ⟨979462808009428642915087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305950410679238190553449 979462808009428642915087)
                      ·
                        rfl

theorem cell23_1907497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 2, 2].length) (baseStart_1907497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907497 prefixEnd_1907497 := by exact prefixLift 1907497
  have htrace : WordTrace (prefixWord ++ tailWord_1907497) baseStart_1907497 baseEnd_1907497 := by
    simpa [prefixWord, tailWord_1907497, baseEnd_1907497] using wordTrace_append hprefix tailTrace_1907497
  have hstable : (prefixWord ++ tailWord_1907497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907497).length < 2 ^ (prefixWord ++ tailWord_1907497).sum := by decide
  have hdescent : baseEnd_1907497 < baseStart_1907497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907500 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_1907500 : Nat := 118140960795 + 1907500 * 2 ^ 59
def prefixEnd_1907500 : Nat := 4983230072969 + 3 ^ 40 * 1907500 * 2
def baseEnd_1907500 : Nat := 979464348451392131177573

theorem tailTrace_1907500 : CollatzResearch.WordTrace tailWord_1907500 prefixEnd_1907500 979464348451392131177573 := by
  unfold tailWord_1907500
  simp only [CollatzResearch.WordTrace]
  refine ⟨34786120294730374954415977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46381493726307166605887969 34786120294730374954415977)
  ·
    refine ⟨26089590221047781215811983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34786120294730374954415977 26089590221047781215811983)
    ·
      refine ⟨39134385331571671823717975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26089590221047781215811983 39134385331571671823717975)
      ·
        refine ⟨58701577997357507735576963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39134385331571671823717975 58701577997357507735576963)
        ·
          refine ⟨88052366996036261603365445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58701577997357507735576963 88052366996036261603365445)
          ·
            refine ⟨16509818811756799050631021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88052366996036261603365445 16509818811756799050631021)
            ·
              refine ⟨6191182054408799643986633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16509818811756799050631021 6191182054408799643986633)
              ·
                refine ⟨4643386540806599732989975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191182054408799643986633 4643386540806599732989975)
                ·
                  refine ⟨6965079811209899599484963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643386540806599732989975 6965079811209899599484963)
                  ·
                    refine ⟨10447619716814849399227445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6965079811209899599484963 10447619716814849399227445)
                    ·
                      refine ⟨979464348451392131177573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10447619716814849399227445 979464348451392131177573)
                      ·
                        rfl

theorem cell23_1907500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_1907500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907500 prefixEnd_1907500 := by exact prefixLift 1907500
  have htrace : WordTrace (prefixWord ++ tailWord_1907500) baseStart_1907500 baseEnd_1907500 := by
    simpa [prefixWord, tailWord_1907500, baseEnd_1907500] using wordTrace_append hprefix tailTrace_1907500
  have hstable : (prefixWord ++ tailWord_1907500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907500).length < 2 ^ (prefixWord ++ tailWord_1907500).sum := by decide
  have hdescent : baseEnd_1907500 < baseStart_1907500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907507 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 1, 6]
def baseStart_1907507 : Nat := 118140960795 + 1907507 * 2 ^ 59
def prefixEnd_1907507 : Nat := 4983230072969 + 3 ^ 40 * 1907507 * 2
def baseEnd_1907507 : Nat := 326489314271991201263347

theorem tailTrace_1907507 : CollatzResearch.WordTrace tailWord_1907507 prefixEnd_1907507 326489314271991201263347 := by
  unfold tailWord_1907507
  simp only [CollatzResearch.WordTrace]
  refine ⟨69572495900435390104336775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46381663933623593402891183 69572495900435390104336775)
  ·
    refine ⟨104358743850653085156505163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69572495900435390104336775 104358743850653085156505163)
    ·
      refine ⟨156538115775979627734757745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104358743850653085156505163 156538115775979627734757745)
      ·
        refine ⟨117403586831984720801068309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156538115775979627734757745 117403586831984720801068309)
        ·
          refine ⟨5503293132749283787550077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117403586831984720801068309 5503293132749283787550077)
          ·
            refine ⟨2063734924780981420331279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5503293132749283787550077 2063734924780981420331279)
            ·
              refine ⟨3095602387171472130496919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063734924780981420331279 3095602387171472130496919)
              ·
                refine ⟨4643403580757208195745379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095602387171472130496919 4643403580757208195745379)
                ·
                  refine ⟨6965105371135812293618069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643403580757208195745379 6965105371135812293618069)
                  ·
                    refine ⟨326489314271991201263347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6965105371135812293618069 326489314271991201263347)
                    ·
                      rfl

theorem cell23_1907507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 6].length) (baseStart_1907507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907507 prefixEnd_1907507 := by exact prefixLift 1907507
  have htrace : WordTrace (prefixWord ++ tailWord_1907507) baseStart_1907507 baseEnd_1907507 := by
    simpa [prefixWord, tailWord_1907507, baseEnd_1907507] using wordTrace_append hprefix tailTrace_1907507
  have hstable : (prefixWord ++ tailWord_1907507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907507).length < 2 ^ (prefixWord ++ tailWord_1907507).sum := by decide
  have hdescent : baseEnd_1907507 < baseStart_1907507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907514 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_1907514 : Nat := 118140960795 + 1907514 * 2 ^ 59
def prefixEnd_1907514 : Nat := 4983230072969 + 3 ^ 40 * 1907514 * 2
def baseEnd_1907514 : Nat := 979471537180555076402509

theorem tailTrace_1907514 : CollatzResearch.WordTrace tailWord_1907514 prefixEnd_1907514 979471537180555076402509 := by
  unfold tailWord_1907514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17393187802852507574960399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46381834140940020199894397 17393187802852507574960399)
  ·
    refine ⟨26089781704278761362440599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17393187802852507574960399 26089781704278761362440599)
    ·
      refine ⟨39134672556418142043660899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26089781704278761362440599 39134672556418142043660899)
      ·
        refine ⟨58702008834627213065491349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39134672556418142043660899 58702008834627213065491349)
        ·
          refine ⟨2751656664123150612444907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58702008834627213065491349 2751656664123150612444907)
          ·
            refine ⟨4127484996184725918667361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751656664123150612444907 4127484996184725918667361)
            ·
              refine ⟨3095613747138544439000521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4127484996184725918667361 3095613747138544439000521)
              ·
                refine ⟨2321710310353908329250391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095613747138544439000521 2321710310353908329250391)
                ·
                  refine ⟨3482565465530862493875587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321710310353908329250391 3482565465530862493875587)
                  ·
                    refine ⟨5223848198296293740813381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3482565465530862493875587 5223848198296293740813381)
                    ·
                      refine ⟨979471537180555076402509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5223848198296293740813381 979471537180555076402509)
                      ·
                        rfl

theorem cell23_1907514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_1907514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907514 prefixEnd_1907514 := by exact prefixLift 1907514
  have htrace : WordTrace (prefixWord ++ tailWord_1907514) baseStart_1907514 baseEnd_1907514 := by
    simpa [prefixWord, tailWord_1907514, baseEnd_1907514] using wordTrace_append hprefix tailTrace_1907514
  have hstable : (prefixWord ++ tailWord_1907514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907514).length < 2 ^ (prefixWord ++ tailWord_1907514).sum := by decide
  have hdescent : baseEnd_1907514 < baseStart_1907514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907537 : List Nat := [1, 2, 2, 1, 7, 1, 9]
def baseStart_1907537 : Nat := 118140960795 + 1907537 * 2 ^ 59
def prefixEnd_1907537 : Nat := 4983230072969 + 3 ^ 40 * 1907537 * 2
def baseEnd_1907537 : Nat := 12092387002908746745863

theorem tailTrace_1907537 : CollatzResearch.WordTrace tailWord_1907537 prefixEnd_1907537 12092387002908746745863 := by
  unfold tailWord_1907537
  simp only [CollatzResearch.WordTrace]
  refine ⟨69573590090326705227928865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46382393393551136818619243 69573590090326705227928865)
  ·
    refine ⟨52180192567745028920946649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69573590090326705227928865 52180192567745028920946649)
    ·
      refine ⟨39135144425808771690709987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52180192567745028920946649 39135144425808771690709987)
      ·
        refine ⟨58702716638713157536064981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39135144425808771690709987 58702716638713157536064981)
        ·
          refine ⟨1375844921219839629751523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58702716638713157536064981 1375844921219839629751523)
          ·
            refine ⟨2063767381829759444627285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375844921219839629751523 2063767381829759444627285)
            ·
              refine ⟨12092387002908746745863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2063767381829759444627285 12092387002908746745863)
              ·
                rfl

theorem cell23_1907537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 9].length) (baseStart_1907537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907537 prefixEnd_1907537 := by exact prefixLift 1907537
  have htrace : WordTrace (prefixWord ++ tailWord_1907537) baseStart_1907537 baseEnd_1907537 := by
    simpa [prefixWord, tailWord_1907537, baseEnd_1907537] using wordTrace_append hprefix tailTrace_1907537
  have hstable : (prefixWord ++ tailWord_1907537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907537).length < 2 ^ (prefixWord ++ tailWord_1907537).sum := by decide
  have hdescent : baseEnd_1907537 < baseStart_1907537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907548 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1907548 : Nat := 118140960795 + 1907548 * 2 ^ 59
def prefixEnd_1907548 : Nat := 4983230072969 + 3 ^ 40 * 1907548 * 2
def baseEnd_1907548 : Nat := 979488995522807943377353

theorem tailTrace_1907548 : CollatzResearch.WordTrace tailWord_1907548 prefixEnd_1907548 979488995522807943377353 := by
  unfold tailWord_1907548
  simp only [CollatzResearch.WordTrace]
  refine ⟨34786995646643427053289649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46382660862191236071052865 34786995646643427053289649)
  ·
    refine ⟨26090246734982570289967237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34786995646643427053289649 26090246734982570289967237)
    ·
      refine ⟨4891921262809231929368857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26090246734982570289967237 4891921262809231929368857)
      ·
        refine ⟨3668940947106923947026643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4891921262809231929368857 3668940947106923947026643)
        ·
          refine ⟨5503411420660385920539965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668940947106923947026643 5503411420660385920539965)
          ·
            refine ⟨2063779282747644720202487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5503411420660385920539965 2063779282747644720202487)
            ·
              refine ⟨3095668924121467080303731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063779282747644720202487 3095668924121467080303731)
              ·
                refine ⟨4643503386182200620455597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095668924121467080303731 4643503386182200620455597)
                ·
                  refine ⟨1741313769818325232670849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4643503386182200620455597 1741313769818325232670849)
                  ·
                    refine ⟨1305985327363743924503137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1741313769818325232670849 1305985327363743924503137)
                    ·
                      refine ⟨979488995522807943377353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1305985327363743924503137 979488995522807943377353)
                      ·
                        rfl

theorem cell23_1907548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1907548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907548 prefixEnd_1907548 := by exact prefixLift 1907548
  have htrace : WordTrace (prefixWord ++ tailWord_1907548) baseStart_1907548 baseEnd_1907548 := by
    simpa [prefixWord, tailWord_1907548, baseEnd_1907548] using wordTrace_append hprefix tailTrace_1907548
  have hstable : (prefixWord ++ tailWord_1907548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907548).length < 2 ^ (prefixWord ++ tailWord_1907548).sum := by decide
  have hdescent : baseEnd_1907548 < baseStart_1907548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907564 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_1907564 : Nat := 118140960795 + 1907564 * 2 ^ 59
def prefixEnd_1907564 : Nat := 4983230072969 + 3 ^ 40 * 1907564 * 2
def baseEnd_1907564 : Nat := 979497211213279880777279

theorem tailTrace_1907564 : CollatzResearch.WordTrace tailWord_1907564 prefixEnd_1907564 979497211213279880777279 := by
  unfold tailWord_1907564
  simp only [CollatzResearch.WordTrace]
  refine ⟨34787287430614444419580873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46383049907485925892774497 34787287430614444419580873)
  ·
    refine ⟨26090465572960833314685655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34787287430614444419580873 26090465572960833314685655)
    ·
      refine ⟨39135698359441249972028483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26090465572960833314685655 39135698359441249972028483)
      ·
        refine ⟨58703547539161874958042725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39135698359441249972028483 58703547539161874958042725)
        ·
          refine ⟨11006915163592851554633011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58703547539161874958042725 11006915163592851554633011)
          ·
            refine ⟨16510372745389277331949517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006915163592851554633011 16510372745389277331949517)
            ·
              refine ⟨6191389779520978999481069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16510372745389277331949517 6191389779520978999481069)
              ·
                refine ⟨2321771167320367124805401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6191389779520978999481069 2321771167320367124805401)
                ·
                  refine ⟨1741328375490275343604051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321771167320367124805401 1741328375490275343604051)
                  ·
                    refine ⟨2611992563235413015406077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741328375490275343604051 2611992563235413015406077)
                    ·
                      refine ⟨979497211213279880777279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2611992563235413015406077 979497211213279880777279)
                      ·
                        rfl

theorem cell23_1907564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_1907564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907564 prefixEnd_1907564 := by exact prefixLift 1907564
  have htrace : WordTrace (prefixWord ++ tailWord_1907564) baseStart_1907564 baseEnd_1907564 := by
    simpa [prefixWord, tailWord_1907564, baseEnd_1907564] using wordTrace_append hprefix tailTrace_1907564
  have hstable : (prefixWord ++ tailWord_1907564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907564).length < 2 ^ (prefixWord ++ tailWord_1907564).sum := by decide
  have hdescent : baseEnd_1907564 < baseStart_1907564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907604 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_1907604 : Nat := 118140960795 + 1907604 * 2 ^ 59
def prefixEnd_1907604 : Nat := 4983230072969 + 3 ^ 40 * 1907604 * 2
def baseEnd_1907604 : Nat := 979517750439459724277095

theorem tailTrace_1907604 : CollatzResearch.WordTrace tailWord_1907604 prefixEnd_1907604 979517750439459724277095 := by
  unfold tailWord_1907604
  simp only [CollatzResearch.WordTrace]
  refine ⟨34788016890541987835308933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46384022520722650447078577 34788016890541987835308933)
  ·
    refine ⟨6522753166976622719120425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34788016890541987835308933 6522753166976622719120425)
    ·
      refine ⟨4892064875232467039340319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6522753166976622719120425 4892064875232467039340319)
      ·
        refine ⟨7338097312848700559010479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892064875232467039340319 7338097312848700559010479)
        ·
          refine ⟨11007145969273050838515719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338097312848700559010479 11007145969273050838515719)
          ·
            refine ⟨16510718953909576257773579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11007145969273050838515719 16510718953909576257773579)
            ·
              refine ⟨24766078430864364386660369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16510718953909576257773579 24766078430864364386660369)
              ·
                refine ⟨18574558823148273289995277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24766078430864364386660369 18574558823148273289995277)
                ·
                  refine ⟨6965459558680602483748229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18574558823148273289995277 6965459558680602483748229)
                  ·
                    refine ⟨1306023667252612965702793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6965459558680602483748229 1306023667252612965702793)
                    ·
                      refine ⟨979517750439459724277095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306023667252612965702793 979517750439459724277095)
                      ·
                        rfl

theorem cell23_1907604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_1907604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907604 prefixEnd_1907604 := by exact prefixLift 1907604
  have htrace : WordTrace (prefixWord ++ tailWord_1907604) baseStart_1907604 baseEnd_1907604 := by
    simpa [prefixWord, tailWord_1907604, baseEnd_1907604] using wordTrace_append hprefix tailTrace_1907604
  have hstable : (prefixWord ++ tailWord_1907604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907604).length < 2 ^ (prefixWord ++ tailWord_1907604).sum := by decide
  have hdescent : baseEnd_1907604 < baseStart_1907604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907617 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1907617 : Nat := 118140960795 + 1907617 * 2 ^ 59
def prefixEnd_1907617 : Nat := 4983230072969 + 3 ^ 40 * 1907617 * 2
def baseEnd_1907617 : Nat := 979524425687968173414535

theorem tailTrace_1907617 : CollatzResearch.WordTrace tailWord_1907617 prefixEnd_1907617 979524425687968173414535 := by
  unfold tailWord_1907617
  simp only [CollatzResearch.WordTrace]
  refine ⟨69576507930036878890841105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46384338620024585927227403 69576507930036878890841105)
  ·
    refine ⟨52182380947527659168130829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69576507930036878890841105 52182380947527659168130829)
    ·
      refine ⟨19568392855322872188049061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52182380947527659168130829 19568392855322872188049061)
      ·
        refine ⟨3669073660373038535259199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19568392855322872188049061 3669073660373038535259199)
        ·
          refine ⟨5503610490559557802888799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669073660373038535259199 5503610490559557802888799)
          ·
            refine ⟨8255415735839336704333199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503610490559557802888799 8255415735839336704333199)
            ·
              refine ⟨12383123603759005056499799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8255415735839336704333199 12383123603759005056499799)
              ·
                refine ⟨18574685405638507584749699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12383123603759005056499799 18574685405638507584749699)
                ·
                  refine ⟨27862028108457761377124549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18574685405638507584749699 27862028108457761377124549)
                  ·
                    refine ⟨5224130270335830258210853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27862028108457761377124549 5224130270335830258210853)
                    ·
                      refine ⟨979524425687968173414535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5224130270335830258210853 979524425687968173414535)
                      ·
                        rfl

theorem cell23_1907617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1907617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907617 prefixEnd_1907617 := by exact prefixLift 1907617
  have htrace : WordTrace (prefixWord ++ tailWord_1907617) baseStart_1907617 baseEnd_1907617 := by
    simpa [prefixWord, tailWord_1907617, baseEnd_1907617] using wordTrace_append hprefix tailTrace_1907617
  have hstable : (prefixWord ++ tailWord_1907617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907617).length < 2 ^ (prefixWord ++ tailWord_1907617).sum := by decide
  have hdescent : baseEnd_1907617 < baseStart_1907617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907637 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1907637 : Nat := 118140960795 + 1907637 * 2 ^ 59
def prefixEnd_1907637 : Nat := 4983230072969 + 3 ^ 40 * 1907637 * 2
def baseEnd_1907637 : Nat := 979534695301058095164443

theorem tailTrace_1907637 : CollatzResearch.WordTrace tailWord_1907637 prefixEnd_1907637 979534695301058095164443 := by
  unfold tailWord_1907637
  simp only [CollatzResearch.WordTrace]
  refine ⟨69577237389964422306569165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46384824926642948204379443 69577237389964422306569165)
  ·
    refine ⟨26091464021236658364963437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69577237389964422306569165 26091464021236658364963437)
    ·
      refine ⟨9784299007963746886861289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26091464021236658364963437 9784299007963746886861289)
      ·
        refine ⟨7338224255972810165145967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9784299007963746886861289 7338224255972810165145967)
        ·
          refine ⟨11007336383959215247718951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338224255972810165145967 11007336383959215247718951)
          ·
            refine ⟨16511004575938822871578427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11007336383959215247718951 16511004575938822871578427)
            ·
              refine ⟨24766506863908234307367641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16511004575938822871578427 24766506863908234307367641)
              ·
                refine ⟨18574880147931175730525731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24766506863908234307367641 18574880147931175730525731)
                ·
                  refine ⟨27862320221896763595788597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18574880147931175730525731 27862320221896763595788597)
                  ·
                    refine ⟨2612092520802821587105181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27862320221896763595788597 2612092520802821587105181)
                    ·
                      refine ⟨979534695301058095164443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612092520802821587105181 979534695301058095164443)
                      ·
                        rfl

theorem cell23_1907637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1907637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907637 prefixEnd_1907637 := by exact prefixLift 1907637
  have htrace : WordTrace (prefixWord ++ tailWord_1907637) baseStart_1907637 baseEnd_1907637 := by
    simpa [prefixWord, tailWord_1907637, baseEnd_1907637] using wordTrace_append hprefix tailTrace_1907637
  have hstable : (prefixWord ++ tailWord_1907637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907637).length < 2 ^ (prefixWord ++ tailWord_1907637).sum := by decide
  have hdescent : baseEnd_1907637 < baseStart_1907637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907647 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 7, 2]
def baseStart_1907647 : Nat := 118140960795 + 1907647 * 2 ^ 59
def prefixEnd_1907647 : Nat := 4983230072969 + 3 ^ 40 * 1907647 * 2
def baseEnd_1907647 : Nat := 979539830107603056039397

theorem tailTrace_1907647 : CollatzResearch.WordTrace tailWord_1907647 prefixEnd_1907647 979539830107603056039397 := by
  unfold tailWord_1907647
  simp only [CollatzResearch.WordTrace]
  refine ⟨69577602119928194014433195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46385068079952129342955463 69577602119928194014433195)
  ·
    refine ⟨104366403179892291021649793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69577602119928194014433195 104366403179892291021649793)
    ·
      refine ⟨78274802384919218266237345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104366403179892291021649793 78274802384919218266237345)
      ·
        refine ⟨58706101788689413699678009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78274802384919218266237345 58706101788689413699678009)
        ·
          refine ⟨44029576341517060274758507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58706101788689413699678009 44029576341517060274758507)
          ·
            refine ⟨66044364512275590412137761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44029576341517060274758507 66044364512275590412137761)
            ·
              refine ⟨49533273384206692809103321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66044364512275590412137761 49533273384206692809103321)
              ·
                refine ⟨37149955038155019606827491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49533273384206692809103321 37149955038155019606827491)
                ·
                  refine ⟨55724932557232529410241237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37149955038155019606827491 55724932557232529410241237)
                  ·
                    refine ⟨1306053106810137408052529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55724932557232529410241237 1306053106810137408052529)
                    ·
                      refine ⟨979539830107603056039397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306053106810137408052529 979539830107603056039397)
                      ·
                        rfl

theorem cell23_1907647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_1907647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907647 prefixEnd_1907647 := by exact prefixLift 1907647
  have htrace : WordTrace (prefixWord ++ tailWord_1907647) baseStart_1907647 baseEnd_1907647 := by
    simpa [prefixWord, tailWord_1907647, baseEnd_1907647] using wordTrace_append hprefix tailTrace_1907647
  have hstable : (prefixWord ++ tailWord_1907647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907647).length < 2 ^ (prefixWord ++ tailWord_1907647).sum := by decide
  have hdescent : baseEnd_1907647 < baseStart_1907647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907717 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 6]
def baseStart_1907717 : Nat := 118140960795 + 1907717 * 2 ^ 59
def prefixEnd_1907717 : Nat := 4983230072969 + 3 ^ 40 * 1907717 * 2
def baseEnd_1907717 : Nat := 108841752639268642462675

theorem tailTrace_1907717 : CollatzResearch.WordTrace tailWord_1907717 prefixEnd_1907717 108841752639268642462675 := by
  unfold tailWord_1907717
  simp only [CollatzResearch.WordTrace]
  refine ⟨69580155229674595969481405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46386770153116397312987603 69580155229674595969481405)
  ·
    refine ⟨26092558211127973488555527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69580155229674595969481405 26092558211127973488555527)
    ·
      refine ⟨39138837316691960232833291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26092558211127973488555527 39138837316691960232833291)
      ·
        refine ⟨58708255975037940349249937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39138837316691960232833291 58708255975037940349249937)
        ·
          refine ⟨44031191981278455261937453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58708255975037940349249937 44031191981278455261937453)
          ·
            refine ⟨16511696992979420723226545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44031191981278455261937453 16511696992979420723226545)
            ·
              refine ⟨12383772744734565542419909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16511696992979420723226545 12383772744734565542419909)
              ·
                refine ⟨2321957389637731039203733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12383772744734565542419909 2321957389637731039203733)
                ·
                  refine ⟨108841752639268642462675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2321957389637731039203733 108841752639268642462675)
                  ·
                    rfl

theorem cell23_1907717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_1907717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907717 prefixEnd_1907717 := by exact prefixLift 1907717
  have htrace : WordTrace (prefixWord ++ tailWord_1907717) baseStart_1907717 baseEnd_1907717 := by
    simpa [prefixWord, tailWord_1907717, baseEnd_1907717] using wordTrace_append hprefix tailTrace_1907717
  have hstable : (prefixWord ++ tailWord_1907717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907717).length < 2 ^ (prefixWord ++ tailWord_1907717).sum := by decide
  have hdescent : baseEnd_1907717 < baseStart_1907717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907787 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 3]
def baseStart_1907787 : Nat := 118140960795 + 1907787 * 2 ^ 59
def prefixEnd_1907787 : Nat := 4983230072969 + 3 ^ 40 * 1907787 * 2
def baseEnd_1907787 : Nat := 979611717399232508288753

theorem tailTrace_1907787 : CollatzResearch.WordTrace tailWord_1907787 prefixEnd_1907787 979611717399232508288753 := by
  unfold tailWord_1907787
  simp only [CollatzResearch.WordTrace]
  refine ⟨69582708339420997924529615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46388472226280665283019743 69582708339420997924529615)
  ·
    refine ⟨104374062509131496886794423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69582708339420997924529615 104374062509131496886794423)
    ·
      refine ⟨156561093763697245330191635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104374062509131496886794423 156561093763697245330191635)
      ·
        refine ⟨234841640645545867995287453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156561093763697245330191635 234841640645545867995287453)
        ·
          refine ⟨88065615242079700498232795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234841640645545867995287453 88065615242079700498232795)
          ·
            refine ⟨132098422863119550747349193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88065615242079700498232795 132098422863119550747349193)
            ·
              refine ⟨99073817147339663060511895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132098422863119550747349193 99073817147339663060511895)
              ·
                refine ⟨148610725721009494590767843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99073817147339663060511895 148610725721009494590767843)
                ·
                  refine ⟨222916088581514241886151765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148610725721009494590767843 222916088581514241886151765)
                  ·
                    refine ⟨2612297913064620022103341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 222916088581514241886151765 2612297913064620022103341)
                    ·
                      refine ⟨979611717399232508288753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612297913064620022103341 979611717399232508288753)
                      ·
                        rfl

theorem cell23_1907787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 3].length) (baseStart_1907787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907787 prefixEnd_1907787 := by exact prefixLift 1907787
  have htrace : WordTrace (prefixWord ++ tailWord_1907787) baseStart_1907787 baseEnd_1907787 := by
    simpa [prefixWord, tailWord_1907787, baseEnd_1907787] using wordTrace_append hprefix tailTrace_1907787
  have hstable : (prefixWord ++ tailWord_1907787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907787).length < 2 ^ (prefixWord ++ tailWord_1907787).sum := by decide
  have hdescent : baseEnd_1907787 < baseStart_1907787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907794 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1907794 : Nat := 118140960795 + 1907794 * 2 ^ 59
def prefixEnd_1907794 : Nat := 4983230072969 + 3 ^ 40 * 1907794 * 2
def baseEnd_1907794 : Nat := 326538437254604660300407

theorem tailTrace_1907794 : CollatzResearch.WordTrace tailWord_1907794 prefixEnd_1907794 326538437254604660300407 := by
  unfold tailWord_1907794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395740912598909530008609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46388642433597092080022957 17395740912598909530008609)
  ·
    refine ⟨13046805684449182147506457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17395740912598909530008609 13046805684449182147506457)
    ·
      refine ⟨9785104263336886610629843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13046805684449182147506457 9785104263336886610629843)
      ·
        refine ⟨14677656395005329915944765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785104263336886610629843 14677656395005329915944765)
        ·
          refine ⟨5504121148126998718479287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14677656395005329915944765 5504121148126998718479287)
          ·
            refine ⟨8256181722190498077718931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504121148126998718479287 8256181722190498077718931)
            ·
              refine ⟨12384272583285747116578397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256181722190498077718931 12384272583285747116578397)
              ·
                refine ⟨4644102218732155168716899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12384272583285747116578397 4644102218732155168716899)
                ·
                  refine ⟨6966153328098232753075349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644102218732155168716899 6966153328098232753075349)
                  ·
                    refine ⟨326538437254604660300407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6966153328098232753075349 326538437254604660300407)
                    ·
                      rfl

theorem cell23_1907794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1907794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907794 prefixEnd_1907794 := by exact prefixLift 1907794
  have htrace : WordTrace (prefixWord ++ tailWord_1907794) baseStart_1907794 baseEnd_1907794 := by
    simpa [prefixWord, tailWord_1907794, baseEnd_1907794] using wordTrace_append hprefix tailTrace_1907794
  have hstable : (prefixWord ++ tailWord_1907794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907794).length < 2 ^ (prefixWord ++ tailWord_1907794).sum := by decide
  have hdescent : baseEnd_1907794 < baseStart_1907794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907818 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_1907818 : Nat := 118140960795 + 1907818 * 2 ^ 59
def prefixEnd_1907818 : Nat := 4983230072969 + 3 ^ 40 * 1907818 * 2
def baseEnd_1907818 : Nat := 979627635299521887001111

theorem tailTrace_1907818 : CollatzResearch.WordTrace tailWord_1907818 prefixEnd_1907818 979627635299521887001111 := by
  unfold tailWord_1907818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395959750577172554727027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46389226001539126812605405 17395959750577172554727027)
  ·
    refine ⟨26093939625865758832090541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17395959750577172554727027 26093939625865758832090541)
    ·
      refine ⟨9785227359699659562033953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26093939625865758832090541 9785227359699659562033953)
      ·
        refine ⟨7338920519774744671525465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9785227359699659562033953 7338920519774744671525465)
        ·
          refine ⟨5504190389831058503644099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7338920519774744671525465 5504190389831058503644099)
          ·
            refine ⟨8256285584746587755466149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504190389831058503644099 8256285584746587755466149)
            ·
              refine ⟨1548053547139985204149903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8256285584746587755466149 1548053547139985204149903)
              ·
                refine ⟨2322080320709977806224855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548053547139985204149903 2322080320709977806224855)
                ·
                  refine ⟨3483120481064966709337283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322080320709977806224855 3483120481064966709337283)
                  ·
                    refine ⟨5224680721597450064005925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3483120481064966709337283 5224680721597450064005925)
                    ·
                      refine ⟨979627635299521887001111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5224680721597450064005925 979627635299521887001111)
                      ·
                        rfl

theorem cell23_1907818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_1907818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907818 prefixEnd_1907818 := by exact prefixLift 1907818
  have htrace : WordTrace (prefixWord ++ tailWord_1907818) baseStart_1907818 baseEnd_1907818 := by
    simpa [prefixWord, tailWord_1907818, baseEnd_1907818] using wordTrace_append hprefix tailTrace_1907818
  have hstable : (prefixWord ++ tailWord_1907818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907818).length < 2 ^ (prefixWord ++ tailWord_1907818).sum := by decide
  have hdescent : baseEnd_1907818 < baseStart_1907818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907848 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1907848 : Nat := 118140960795 + 1907848 * 2 ^ 59
def prefixEnd_1907848 : Nat := 4983230072969 + 3 ^ 40 * 1907848 * 2
def baseEnd_1907848 : Nat := 979643039719156769625973

theorem tailTrace_1907848 : CollatzResearch.WordTrace tailWord_1907848 prefixEnd_1907848 979643039719156769625973 := by
  unfold tailWord_1907848
  simp only [CollatzResearch.WordTrace]
  refine ⟨34792466596100002671250099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46389955461466670228333465 34792466596100002671250099)
  ·
    refine ⟨52188699894150004006875149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34792466596100002671250099 52188699894150004006875149)
    ·
      refine ⟨19570762460306251502578181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52188699894150004006875149 19570762460306251502578181)
      ·
        refine ⟨3669517961307422156733409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19570762460306251502578181 3669517961307422156733409)
        ·
          refine ⟨2752138470980566617550057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669517961307422156733409 2752138470980566617550057)
          ·
            refine ⟨2064103853235424963162543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2752138470980566617550057 2064103853235424963162543)
            ·
              refine ⟨3096155779853137444743815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064103853235424963162543 3096155779853137444743815)
              ·
                refine ⟨4644233669779706167115723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096155779853137444743815 4644233669779706167115723)
                ·
                  refine ⟨6966350504669559250673585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644233669779706167115723 6966350504669559250673585)
                  ·
                    refine ⟨5224762878502169438005189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6966350504669559250673585 5224762878502169438005189)
                    ·
                      refine ⟨979643039719156769625973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5224762878502169438005189 979643039719156769625973)
                      ·
                        rfl

theorem cell23_1907848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1907848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907848 prefixEnd_1907848 := by exact prefixLift 1907848
  have htrace : WordTrace (prefixWord ++ tailWord_1907848) baseStart_1907848 baseEnd_1907848 := by
    simpa [prefixWord, tailWord_1907848, baseEnd_1907848] using wordTrace_append hprefix tailTrace_1907848
  have hstable : (prefixWord ++ tailWord_1907848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907848).length < 2 ^ (prefixWord ++ tailWord_1907848).sum := by decide
  have hdescent : baseEnd_1907848 < baseStart_1907848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907851 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 3]
def baseStart_1907851 : Nat := 118140960795 + 1907851 * 2 ^ 59
def prefixEnd_1907851 : Nat := 4983230072969 + 3 ^ 40 * 1907851 * 2
def baseEnd_1907851 : Nat := 979644580161120257888459

theorem tailTrace_1907851 : CollatzResearch.WordTrace tailWord_1907851 prefixEnd_1907851 979644580161120257888459 := by
  unfold tailWord_1907851
  simp only [CollatzResearch.WordTrace]
  refine ⟨69585042611189136854859407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46390028407459424569906271 69585042611189136854859407)
  ·
    refine ⟨104377563916783705282289111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69585042611189136854859407 104377563916783705282289111)
    ·
      refine ⟨156566345875175557923433667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104377563916783705282289111 156566345875175557923433667)
      ·
        refine ⟨234849518812763336885150501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156566345875175557923433667 234849518812763336885150501)
        ·
          refine ⟨44034284777393125665965719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234849518812763336885150501 44034284777393125665965719)
          ·
            refine ⟨66051427166089688498948579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44034284777393125665965719 66051427166089688498948579)
            ·
              refine ⟨99077140749134532748422869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66051427166089688498948579 99077140749134532748422869)
              ·
                refine ⟨2322120486307840611291161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 99077140749134532748422869 2322120486307840611291161)
                ·
                  refine ⟨1741590364730880458468371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322120486307840611291161 1741590364730880458468371)
                  ·
                    refine ⟨2612385547096320687702557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741590364730880458468371 2612385547096320687702557)
                    ·
                      refine ⟨979644580161120257888459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612385547096320687702557 979644580161120257888459)
                      ·
                        rfl

theorem cell23_1907851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 3].length) (baseStart_1907851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907851 prefixEnd_1907851 := by exact prefixLift 1907851
  have htrace : WordTrace (prefixWord ++ tailWord_1907851) baseStart_1907851 baseEnd_1907851 := by
    simpa [prefixWord, tailWord_1907851, baseEnd_1907851] using wordTrace_append hprefix tailTrace_1907851
  have hstable : (prefixWord ++ tailWord_1907851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907851).length < 2 ^ (prefixWord ++ tailWord_1907851).sum := by decide
  have hdescent : baseEnd_1907851 < baseStart_1907851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907864 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1907864 : Nat := 118140960795 + 1907864 * 2 ^ 59
def prefixEnd_1907864 : Nat := 4983230072969 + 3 ^ 40 * 1907864 * 2
def baseEnd_1907864 : Nat := 979651255409628707025899

theorem tailTrace_1907864 : CollatzResearch.WordTrace tailWord_1907864 prefixEnd_1907864 979651255409628707025899 := by
  unfold tailWord_1907864
  simp only [CollatzResearch.WordTrace]
  refine ⟨34792758380071020037541323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46390344506761360050055097 34792758380071020037541323)
  ·
    refine ⟨52189137570106530056311985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34792758380071020037541323 52189137570106530056311985)
    ·
      refine ⟨39141853177579897542233989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52189137570106530056311985 39141853177579897542233989)
      ·
        refine ⟨7339097470796230789168873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39141853177579897542233989 7339097470796230789168873)
        ·
          refine ⟨5504323103097173091876655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7339097470796230789168873 5504323103097173091876655)
          ·
            refine ⟨8256484654645759637814983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504323103097173091876655 8256484654645759637814983)
            ·
              refine ⟨12384726981968639456722475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256484654645759637814983 12384726981968639456722475)
              ·
                refine ⟨18577090472952959185083713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12384726981968639456722475 18577090472952959185083713)
                ·
                  refine ⟨13932817854714719388812785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18577090472952959185083713 13932817854714719388812785)
                  ·
                    refine ⟨10449613391036039541609589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13932817854714719388812785 10449613391036039541609589)
                    ·
                      refine ⟨979651255409628707025899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10449613391036039541609589 979651255409628707025899)
                      ·
                        rfl

theorem cell23_1907864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1907864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907864 prefixEnd_1907864 := by exact prefixLift 1907864
  have htrace : WordTrace (prefixWord ++ tailWord_1907864) baseStart_1907864 baseEnd_1907864 := by
    simpa [prefixWord, tailWord_1907864, baseEnd_1907864] using wordTrace_append hprefix tailTrace_1907864
  have hstable : (prefixWord ++ tailWord_1907864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907864).length < 2 ^ (prefixWord ++ tailWord_1907864).sum := by decide
  have hdescent : baseEnd_1907864 < baseStart_1907864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907867 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 6, 6]
def baseStart_1907867 : Nat := 118140960795 + 1907867 * 2 ^ 59
def prefixEnd_1907867 : Nat := 4983230072969 + 3 ^ 40 * 1907867 * 2
def baseEnd_1907867 : Nat := 326550931950530731762795

theorem tailTrace_1907867 : CollatzResearch.WordTrace tailWord_1907867 prefixEnd_1907867 326550931950530731762795 := by
  unfold tailWord_1907867
  simp only [CollatzResearch.WordTrace]
  refine ⟨69585626179131171587441855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46390417452754114391627903 69585626179131171587441855)
  ·
    refine ⟨104378439268696757381162783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69585626179131171587441855 104378439268696757381162783)
    ·
      refine ⟨156567658903045136071744175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104378439268696757381162783 156567658903045136071744175)
      ·
        refine ⟨234851488354567704107616263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156567658903045136071744175 234851488354567704107616263)
        ·
          refine ⟨352277232531851556161424395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234851488354567704107616263 352277232531851556161424395)
          ·
            refine ⟨528415848797777334242136593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352277232531851556161424395 528415848797777334242136593)
            ·
              refine ⟨396311886598333000681602445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528415848797777334242136593 396311886598333000681602445)
              ·
                refine ⟨148616957474374875255600917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396311886598333000681602445 148616957474374875255600917)
                ·
                  refine ⟨6966419881611322277606293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148616957474374875255600917 6966419881611322277606293)
                  ·
                    refine ⟨326550931950530731762795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6966419881611322277606293 326550931950530731762795)
                    ·
                      rfl

theorem cell23_1907867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 6].length) (baseStart_1907867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907867 prefixEnd_1907867 := by exact prefixLift 1907867
  have htrace : WordTrace (prefixWord ++ tailWord_1907867) baseStart_1907867 baseEnd_1907867 := by
    simpa [prefixWord, tailWord_1907867, baseEnd_1907867] using wordTrace_append hprefix tailTrace_1907867
  have hstable : (prefixWord ++ tailWord_1907867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907867).length < 2 ^ (prefixWord ++ tailWord_1907867).sum := by decide
  have hdescent : baseEnd_1907867 < baseStart_1907867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907902 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_1907902 : Nat := 118140960795 + 1907902 * 2 ^ 59
def prefixEnd_1907902 : Nat := 4983230072969 + 3 ^ 40 * 1907902 * 2
def baseEnd_1907902 : Nat := 979670767674499558350725

theorem tailTrace_1907902 : CollatzResearch.WordTrace tailWord_1907902 prefixEnd_1907902 979670767674499558350725 := by
  unfold tailWord_1907902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8698362841750546570620745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46391268489336248376643973 8698362841750546570620745)
  ·
    refine ⟨6523772131312909927965559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8698362841750546570620745 6523772131312909927965559)
    ·
      refine ⟨9785658196969364891948339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6523772131312909927965559 9785658196969364891948339)
      ·
        refine ⟨14678487295454047337922509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785658196969364891948339 14678487295454047337922509)
        ·
          refine ⟨5504432735795267751720941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14678487295454047337922509 5504432735795267751720941)
          ·
            refine ⟨2064162275923225406895353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5504432735795267751720941 2064162275923225406895353)
            ·
              refine ⟨1548121706942419055171515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064162275923225406895353 1548121706942419055171515)
              ·
                refine ⟨2322182560413628582757273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548121706942419055171515 2322182560413628582757273)
                ·
                  refine ⟨1741636920310221437067955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322182560413628582757273 1741636920310221437067955)
                  ·
                    refine ⟨2612455380465332155601933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741636920310221437067955 2612455380465332155601933)
                    ·
                      refine ⟨979670767674499558350725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612455380465332155601933 979670767674499558350725)
                      ·
                        rfl

theorem cell23_1907902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_1907902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907902 prefixEnd_1907902 := by exact prefixLift 1907902
  have htrace : WordTrace (prefixWord ++ tailWord_1907902) baseStart_1907902 baseEnd_1907902 := by
    simpa [prefixWord, tailWord_1907902, baseEnd_1907902] using wordTrace_append hprefix tailTrace_1907902
  have hstable : (prefixWord ++ tailWord_1907902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907902).length < 2 ^ (prefixWord ++ tailWord_1907902).sum := by decide
  have hdescent : baseEnd_1907902 < baseStart_1907902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907948 : List Nat := [2, 2, 1, 1, 2, 4, 4, 2, 5]
def baseStart_1907948 : Nat := 118140960795 + 1907948 * 2 ^ 59
def prefixEnd_1907948 : Nat := 4983230072969 + 3 ^ 40 * 1907948 * 2
def baseEnd_1907948 : Nat := 108854931976067375375057

theorem tailTrace_1907948 : CollatzResearch.WordTrace tailWord_1907948 prefixEnd_1907948 108854931976067375375057 := by
  unfold tailWord_1907948
  simp only [CollatzResearch.WordTrace]
  refine ⟨34794290245918861210570249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46392386994558481614093665 34794290245918861210570249)
  ·
    refine ⟨26095717684439145907927687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34794290245918861210570249 26095717684439145907927687)
    ·
      refine ⟨39143576526658718861891531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26095717684439145907927687 39143576526658718861891531)
      ·
        refine ⟨58715364789988078292837297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39143576526658718861891531 58715364789988078292837297)
        ·
          refine ⟨44036523592491058719627973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58715364789988078292837297 44036523592491058719627973)
          ·
            refine ⟨8256848173592073509930245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44036523592491058719627973 8256848173592073509930245)
            ·
              refine ⟨1548159032548513783111921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8256848173592073509930245 1548159032548513783111921)
              ·
                refine ⟨1161119274411385337333941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548159032548513783111921 1161119274411385337333941)
                ·
                  refine ⟨108854931976067375375057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161119274411385337333941 108854931976067375375057)
                  ·
                    rfl

theorem cell23_1907948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_1907948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907948 prefixEnd_1907948 := by exact prefixLift 1907948
  have htrace : WordTrace (prefixWord ++ tailWord_1907948) baseStart_1907948 baseEnd_1907948 := by
    simpa [prefixWord, tailWord_1907948, baseEnd_1907948] using wordTrace_append hprefix tailTrace_1907948
  have hstable : (prefixWord ++ tailWord_1907948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907948).length < 2 ^ (prefixWord ++ tailWord_1907948).sum := by decide
  have hdescent : baseEnd_1907948 < baseStart_1907948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907991 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 5, 4]
def baseStart_1907991 : Nat := 118140960795 + 1907991 * 2 ^ 59
def prefixEnd_1907991 : Nat := 4983230072969 + 3 ^ 40 * 1907991 * 2
def baseEnd_1907991 : Nat := 326572155817583236712605

theorem tailTrace_1907991 : CollatzResearch.WordTrace tailWord_1907991 prefixEnd_1907991 326572155817583236712605 := by
  unfold tailWord_1907991
  simp only [CollatzResearch.WordTrace]
  refine ⟨69590148830681940764955827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46393432553787960509970551 69590148830681940764955827)
  ·
    refine ⟨104385223246022911147433741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69590148830681940764955827 104385223246022911147433741)
    ·
      refine ⟨39144458717258591680287653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104385223246022911147433741 39144458717258591680287653)
      ·
        refine ⟨7339586009485985940053935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39144458717258591680287653 7339586009485985940053935)
        ·
          refine ⟨11009379014228978910080903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7339586009485985940053935 11009379014228978910080903)
          ·
            refine ⟨16514068521343468365121355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11009379014228978910080903 16514068521343468365121355)
            ·
              refine ⟨24771102782015202547682033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16514068521343468365121355 24771102782015202547682033)
              ·
                refine ⟨18578327086511401910761525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24771102782015202547682033 18578327086511401910761525)
                ·
                  refine ⟨1741718164360443929133893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18578327086511401910761525 1741718164360443929133893)
                  ·
                    refine ⟨326572155817583236712605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1741718164360443929133893 326572155817583236712605)
                    ·
                      rfl

theorem cell23_1907991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_1907991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1907991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1907991 prefixEnd_1907991 := by exact prefixLift 1907991
  have htrace : WordTrace (prefixWord ++ tailWord_1907991) baseStart_1907991 baseEnd_1907991 := by
    simpa [prefixWord, tailWord_1907991, baseEnd_1907991] using wordTrace_append hprefix tailTrace_1907991
  have hstable : (prefixWord ++ tailWord_1907991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907991).length < 2 ^ (prefixWord ++ tailWord_1907991).sum := by decide
  have hdescent : baseEnd_1907991 < baseStart_1907991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908001 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1908001 : Nat := 118140960795 + 1908001 * 2 ^ 59
def prefixEnd_1908001 : Nat := 4983230072969 + 3 ^ 40 * 1908001 * 2
def baseEnd_1908001 : Nat := 979721602259294671012769

theorem tailTrace_1908001 : CollatzResearch.WordTrace tailWord_1908001 prefixEnd_1908001 979721602259294671012769 := by
  unfold tailWord_1908001
  simp only [CollatzResearch.WordTrace]
  refine ⟨69590513560645712472819857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46393675707097141648546571 69590513560645712472819857)
  ·
    refine ⟨52192885170484284354614893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69590513560645712472819857 52192885170484284354614893)
    ·
      refine ⟨19572331938931606632980585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52192885170484284354614893 19572331938931606632980585)
      ·
        refine ⟨14679248954198704974735439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19572331938931606632980585 14679248954198704974735439)
        ·
          refine ⟨22018873431298057462103159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679248954198704974735439 22018873431298057462103159)
          ·
            refine ⟨33028310146947086193154739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22018873431298057462103159 33028310146947086193154739)
            ·
              refine ⟨49542465220420629289732109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33028310146947086193154739 49542465220420629289732109)
              ·
                refine ⟨18578424457657735983649541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49542465220420629289732109 18578424457657735983649541)
                ·
                  refine ⟨3483454585810825496934289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18578424457657735983649541 3483454585810825496934289)
                  ·
                    refine ⟨2612590939358119122700717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3483454585810825496934289 2612590939358119122700717)
                    ·
                      refine ⟨979721602259294671012769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612590939358119122700717 979721602259294671012769)
                      ·
                        rfl

theorem cell23_1908001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1908001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908001 prefixEnd_1908001 := by exact prefixLift 1908001
  have htrace : WordTrace (prefixWord ++ tailWord_1908001) baseStart_1908001 baseEnd_1908001 := by
    simpa [prefixWord, tailWord_1908001, baseEnd_1908001] using wordTrace_append hprefix tailTrace_1908001
  have hstable : (prefixWord ++ tailWord_1908001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908001).length < 2 ^ (prefixWord ++ tailWord_1908001).sum := by decide
  have hdescent : baseEnd_1908001 < baseStart_1908001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908008 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1908008 : Nat := 118140960795 + 1908008 * 2 ^ 59
def prefixEnd_1908008 : Nat := 4983230072969 + 3 ^ 40 * 1908008 * 2
def baseEnd_1908008 : Nat := 326575065541292047875079

theorem tailTrace_1908008 : CollatzResearch.WordTrace tailWord_1908008 prefixEnd_1908008 326575065541292047875079 := by
  unfold tailWord_1908008
  simp only [CollatzResearch.WordTrace]
  refine ⟨34795384435810176334162339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46393845914413568445549785 34795384435810176334162339)
  ·
    refine ⟨52193076653715264501243509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34795384435810176334162339 52193076653715264501243509)
    ·
      refine ⟨4893100936285806046991579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52193076653715264501243509 4893100936285806046991579)
      ·
        refine ⟨7339651404428709070487369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4893100936285806046991579 7339651404428709070487369)
        ·
          refine ⟨5504738553321531802865527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7339651404428709070487369 5504738553321531802865527)
          ·
            refine ⟨8257107829982297704298291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504738553321531802865527 8257107829982297704298291)
            ·
              refine ⟨12385661744973446556447437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257107829982297704298291 12385661744973446556447437)
              ·
                refine ⟨4644623154365042458667789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12385661744973446556447437 4644623154365042458667789)
                ·
                  refine ⟨1741733682886890922000421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4644623154365042458667789 1741733682886890922000421)
                  ·
                    refine ⟨326575065541292047875079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1741733682886890922000421 326575065541292047875079)
                    ·
                      rfl

theorem cell23_1908008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1908008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908008 prefixEnd_1908008 := by exact prefixLift 1908008
  have htrace : WordTrace (prefixWord ++ tailWord_1908008) baseStart_1908008 baseEnd_1908008 := by
    simpa [prefixWord, tailWord_1908008, baseEnd_1908008] using wordTrace_append hprefix tailTrace_1908008
  have hstable : (prefixWord ++ tailWord_1908008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908008).length < 2 ^ (prefixWord ++ tailWord_1908008).sum := by decide
  have hdescent : baseEnd_1908008 < baseStart_1908008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908024 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1908024 : Nat := 118140960795 + 1908024 * 2 ^ 59
def prefixEnd_1908024 : Nat := 4983230072969 + 3 ^ 40 * 1908024 * 2
def baseEnd_1908024 : Nat := 979733412314348081025163

theorem tailTrace_1908024 : CollatzResearch.WordTrace tailWord_1908024 prefixEnd_1908024 979733412314348081025163 := by
  unfold tailWord_1908024
  simp only [CollatzResearch.WordTrace]
  refine ⟨34795676219781193700453563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46394234959708258267271417 34795676219781193700453563)
  ·
    refine ⟨52193514329671790550680345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34795676219781193700453563 52193514329671790550680345)
    ·
      refine ⟨39145135747253842913010259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52193514329671790550680345 39145135747253842913010259)
      ·
        refine ⟨58717703620880764369515389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39145135747253842913010259 58717703620880764369515389)
        ·
          refine ⟨22019138857830286638568271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58717703620880764369515389 22019138857830286638568271)
          ·
            refine ⟨33028708286745429957852407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22019138857830286638568271 33028708286745429957852407)
            ·
              refine ⟨49543062430118144936778611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33028708286745429957852407 49543062430118144936778611)
              ·
                refine ⟨74314593645177217405167917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49543062430118144936778611 74314593645177217405167917)
                ·
                  refine ⟨27867972616941456526937969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74314593645177217405167917 27867972616941456526937969)
                  ·
                    refine ⟨20900979462706092395203477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27867972616941456526937969 20900979462706092395203477)
                    ·
                      refine ⟨979733412314348081025163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20900979462706092395203477 979733412314348081025163)
                      ·
                        rfl

theorem cell23_1908024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1908024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908024 prefixEnd_1908024 := by exact prefixLift 1908024
  have htrace : WordTrace (prefixWord ++ tailWord_1908024) baseStart_1908024 baseEnd_1908024 := by
    simpa [prefixWord, tailWord_1908024, baseEnd_1908024] using wordTrace_append hprefix tailTrace_1908024
  have hstable : (prefixWord ++ tailWord_1908024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908024).length < 2 ^ (prefixWord ++ tailWord_1908024).sum := by decide
  have hdescent : baseEnd_1908024 < baseStart_1908024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908051 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 1, 5]
def baseStart_1908051 : Nat := 118140960795 + 1908051 * 2 ^ 59
def prefixEnd_1908051 : Nat := 4983230072969 + 3 ^ 40 * 1908051 * 2
def baseEnd_1908051 : Nat := 326582425430673158462513

theorem tailTrace_1908051 : CollatzResearch.WordTrace tailWord_1908051 prefixEnd_1908051 326582425430673158462513 := by
  unfold tailWord_1908051
  simp only [CollatzResearch.WordTrace]
  refine ⟨69592337210464571012140007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46394891473643047341426671 69592337210464571012140007)
  ·
    refine ⟨104388505815696856518210011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69592337210464571012140007 104388505815696856518210011)
    ·
      refine ⟨156582758723545284777315017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104388505815696856518210011 156582758723545284777315017)
      ·
        refine ⟨117437069042658963582986263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156582758723545284777315017 117437069042658963582986263)
        ·
          refine ⟨176155603563988445374479395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117437069042658963582986263 176155603563988445374479395)
          ·
            refine ⟨264233405345982668061719093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176155603563988445374479395 264233405345982668061719093)
            ·
              refine ⟨24771881751185875130786165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264233405345982668061719093 24771881751185875130786165)
              ·
                refine ⟨2322363914173675793511203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24771881751185875130786165 2322363914173675793511203)
                ·
                  refine ⟨3483545871260513690266805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322363914173675793511203 3483545871260513690266805)
                  ·
                    refine ⟨326582425430673158462513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3483545871260513690266805 326582425430673158462513)
                    ·
                      rfl

theorem cell23_1908051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 5].length) (baseStart_1908051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908051 prefixEnd_1908051 := by exact prefixLift 1908051
  have htrace : WordTrace (prefixWord ++ tailWord_1908051) baseStart_1908051 baseEnd_1908051 := by
    simpa [prefixWord, tailWord_1908051, baseEnd_1908051] using wordTrace_append hprefix tailTrace_1908051
  have hstable : (prefixWord ++ tailWord_1908051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908051).length < 2 ^ (prefixWord ++ tailWord_1908051).sum := by decide
  have hdescent : baseEnd_1908051 < baseStart_1908051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908058 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2]
def baseStart_1908058 : Nat := 118140960795 + 1908058 * 2 ^ 59
def prefixEnd_1908058 : Nat := 4983230072969 + 3 ^ 40 * 1908058 * 2
def baseEnd_1908058 : Nat := 979750870656600948000007

theorem tailTrace_1908058 : CollatzResearch.WordTrace tailWord_1908058 prefixEnd_1908058 979750870656600948000007 := by
  unfold tailWord_1908058
  simp only [CollatzResearch.WordTrace]
  refine ⟨17398148130359802801911207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46395061680959474138429885 17398148130359802801911207)
  ·
    refine ⟨26097222195539704202866811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17398148130359802801911207 26097222195539704202866811)
    ·
      refine ⟨39145833293309556304300217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26097222195539704202866811 39145833293309556304300217)
      ·
        refine ⟨29359374969982167228225163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39145833293309556304300217 29359374969982167228225163)
        ·
          refine ⟨44039062454973250842337745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29359374969982167228225163 44039062454973250842337745)
          ·
            refine ⟨33029296841229938131753309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44039062454973250842337745 33029296841229938131753309)
            ·
              refine ⟨12385986315461226799407491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33029296841229938131753309 12385986315461226799407491)
              ·
                refine ⟨18578979473191840199111237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12385986315461226799407491 18578979473191840199111237)
                ·
                  refine ⟨3483558651223470037333357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18578979473191840199111237 3483558651223470037333357)
                  ·
                    refine ⟨1306334494208801264000009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3483558651223470037333357 1306334494208801264000009)
                    ·
                      refine ⟨979750870656600948000007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306334494208801264000009 979750870656600948000007)
                      ·
                        rfl

theorem cell23_1908058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_1908058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908058 prefixEnd_1908058 := by exact prefixLift 1908058
  have htrace : WordTrace (prefixWord ++ tailWord_1908058) baseStart_1908058 baseEnd_1908058 := by
    simpa [prefixWord, tailWord_1908058, baseEnd_1908058] using wordTrace_append hprefix tailTrace_1908058
  have hstable : (prefixWord ++ tailWord_1908058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908058).length < 2 ^ (prefixWord ++ tailWord_1908058).sum := by decide
  have hdescent : baseEnd_1908058 < baseStart_1908058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908065 : List Nat := [1, 2, 3, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_1908065 : Nat := 118140960795 + 1908065 * 2 ^ 59
def prefixEnd_1908065 : Nat := 4983230072969 + 3 ^ 40 * 1908065 * 2
def baseEnd_1908065 : Nat := 979754465021182420612475

theorem tailTrace_1908065 : CollatzResearch.WordTrace tailWord_1908065 prefixEnd_1908065 979754465021182420612475 := by
  unfold tailWord_1908065
  simp only [CollatzResearch.WordTrace]
  refine ⟨69592847832413851403149649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46395231888275900935433099 69592847832413851403149649)
  ·
    refine ⟨52194635874310388552362237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69592847832413851403149649 52194635874310388552362237)
    ·
      refine ⟨19572988452866395707135839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52194635874310388552362237 19572988452866395707135839)
      ·
        refine ⟨29359482679299593560703759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19572988452866395707135839 29359482679299593560703759)
        ·
          refine ⟨44039224018949390341055639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29359482679299593560703759 44039224018949390341055639)
          ·
            refine ⟨66058836028424085511583459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44039224018949390341055639 66058836028424085511583459)
            ·
              refine ⟨99088254042636128267375189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66058836028424085511583459 99088254042636128267375189)
              ·
                refine ⟨1161190477062142128133303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 99088254042636128267375189 1161190477062142128133303)
                ·
                  refine ⟨1741785715593213192199955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161190477062142128133303 1741785715593213192199955)
                  ·
                    refine ⟨2612678573389819788299933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741785715593213192199955 2612678573389819788299933)
                    ·
                      refine ⟨979754465021182420612475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612678573389819788299933 979754465021182420612475)
                      ·
                        rfl

theorem cell23_1908065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_1908065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908065 prefixEnd_1908065 := by exact prefixLift 1908065
  have htrace : WordTrace (prefixWord ++ tailWord_1908065) baseStart_1908065 baseEnd_1908065 := by
    simpa [prefixWord, tailWord_1908065, baseEnd_1908065] using wordTrace_append hprefix tailTrace_1908065
  have hstable : (prefixWord ++ tailWord_1908065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908065).length < 2 ^ (prefixWord ++ tailWord_1908065).sum := by decide
  have hdescent : baseEnd_1908065 < baseStart_1908065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908072 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 6]
def baseStart_1908072 : Nat := 118140960795 + 1908072 * 2 ^ 59
def prefixEnd_1908072 : Nat := 4983230072969 + 3 ^ 40 * 1908072 * 2
def baseEnd_1908072 : Nat := 108862006598418210358327

theorem tailTrace_1908072 : CollatzResearch.WordTrace tailWord_1908072 prefixEnd_1908072 108862006598418210358327 := by
  unfold tailWord_1908072
  simp only [CollatzResearch.WordTrace]
  refine ⟨34796551571694245799327235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46395402095592327732436313 34796551571694245799327235)
  ·
    refine ⟨52194827357541368698990853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34796551571694245799327235 52194827357541368698990853)
    ·
      refine ⟨9786530129539006631060785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52194827357541368698990853 9786530129539006631060785)
      ·
        refine ⟨7339897597154254973295589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9786530129539006631060785 7339897597154254973295589)
        ·
          refine ⟨1376230799466422807492923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7339897597154254973295589 1376230799466422807492923)
          ·
            refine ⟨2064346199199634211239385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376230799466422807492923 2064346199199634211239385)
            ·
              refine ⟨1548259649399725658429539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064346199199634211239385 1548259649399725658429539)
              ·
                refine ⟨2322389474099588487644309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548259649399725658429539 2322389474099588487644309)
                ·
                  refine ⟨108862006598418210358327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2322389474099588487644309 108862006598418210358327)
                  ·
                    rfl

theorem cell23_1908072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 6].length) (baseStart_1908072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908072 prefixEnd_1908072 := by exact prefixLift 1908072
  have htrace : WordTrace (prefixWord ++ tailWord_1908072) baseStart_1908072 baseEnd_1908072 := by
    simpa [prefixWord, tailWord_1908072, baseEnd_1908072] using wordTrace_append hprefix tailTrace_1908072
  have hstable : (prefixWord ++ tailWord_1908072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908072).length < 2 ^ (prefixWord ++ tailWord_1908072).sum := by decide
  have hdescent : baseEnd_1908072 < baseStart_1908072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908101 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_1908101 : Nat := 118140960795 + 1908101 * 2 ^ 59
def prefixEnd_1908101 : Nat := 4983230072969 + 3 ^ 40 * 1908101 * 2
def baseEnd_1908101 : Nat := 979772950324744279762309

theorem tailTrace_1908101 : CollatzResearch.WordTrace tailWord_1908101 prefixEnd_1908101 979772950324744279762309 := by
  unfold tailWord_1908101
  simp only [CollatzResearch.WordTrace]
  refine ⟨69594160860283429551460157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46396107240188953034306771 69594160860283429551460157)
  ·
    refine ⟨26097810322606286081797559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69594160860283429551460157 26097810322606286081797559)
    ·
      refine ⟨39146715483909429122696339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26097810322606286081797559 39146715483909429122696339)
      ·
        refine ⟨58720073225864143684044509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39146715483909429122696339 58720073225864143684044509)
        ·
          refine ⟨22020027459699053881516691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58720073225864143684044509 22020027459699053881516691)
          ·
            refine ⟨33030041189548580822275037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22020027459699053881516691 33030041189548580822275037)
            ·
              refine ⟨12386265446080717808353139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33030041189548580822275037 12386265446080717808353139)
              ·
                refine ⟨18579398169121076712529709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386265446080717808353139 18579398169121076712529709)
                ·
                  refine ⟨6967274313420403767198641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18579398169121076712529709 6967274313420403767198641)
                  ·
                    refine ⟨5225455735065302825398981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6967274313420403767198641 5225455735065302825398981)
                    ·
                      refine ⟨979772950324744279762309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5225455735065302825398981 979772950324744279762309)
                      ·
                        rfl

theorem cell23_1908101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_1908101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908101 prefixEnd_1908101 := by exact prefixLift 1908101
  have htrace : WordTrace (prefixWord ++ tailWord_1908101) baseStart_1908101 baseEnd_1908101 := by
    simpa [prefixWord, tailWord_1908101, baseEnd_1908101] using wordTrace_append hprefix tailTrace_1908101
  have hstable : (prefixWord ++ tailWord_1908101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908101).length < 2 ^ (prefixWord ++ tailWord_1908101).sum := by decide
  have hdescent : baseEnd_1908101 < baseStart_1908101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908116 : List Nat := [2, 4, 2, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_1908116 : Nat := 118140960795 + 1908116 * 2 ^ 59
def prefixEnd_1908116 : Nat := 4983230072969 + 3 ^ 40 * 1908116 * 2
def baseEnd_1908116 : Nat := 979780652534561721074741

theorem tailTrace_1908116 : CollatzResearch.WordTrace tailWord_1908116 prefixEnd_1908116 979780652534561721074741 := by
  unfold tailWord_1908116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34797353977614543556628101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46396471970152724742170801 34797353977614543556628101)
  ·
    refine ⟨6524503870802726916867769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34797353977614543556628101 6524503870802726916867769)
    ·
      refine ⟨4893377903102045187650827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6524503870802726916867769 4893377903102045187650827)
      ·
        refine ⟨7340066854653067781476241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4893377903102045187650827 7340066854653067781476241)
        ·
          refine ⟨5505050140989800836107181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7340066854653067781476241 5505050140989800836107181)
          ·
            refine ⟨2064393802871175313540193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5505050140989800836107181 2064393802871175313540193)
            ·
              refine ⟨1548295352153381485155145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064393802871175313540193 1548295352153381485155145)
              ·
                refine ⟨1161221514115036113866359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548295352153381485155145 1161221514115036113866359)
                ·
                  refine ⟨1741832271172554170799539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161221514115036113866359 1741832271172554170799539)
                  ·
                    refine ⟨2612748406758831256199309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741832271172554170799539 2612748406758831256199309)
                    ·
                      refine ⟨979780652534561721074741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612748406758831256199309 979780652534561721074741)
                      ·
                        rfl

theorem cell23_1908116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_1908116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908116 prefixEnd_1908116 := by exact prefixLift 1908116
  have htrace : WordTrace (prefixWord ++ tailWord_1908116) baseStart_1908116 baseEnd_1908116 := by
    simpa [prefixWord, tailWord_1908116, baseEnd_1908116] using wordTrace_append hprefix tailTrace_1908116
  have hstable : (prefixWord ++ tailWord_1908116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908116).length < 2 ^ (prefixWord ++ tailWord_1908116).sum := by decide
  have hdescent : baseEnd_1908116 < baseStart_1908116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908151 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1908151 : Nat := 118140960795 + 1908151 * 2 ^ 59
def prefixEnd_1908151 : Nat := 4983230072969 + 3 ^ 40 * 1908151 * 2
def baseEnd_1908151 : Nat := 979798624357469084137079

theorem tailTrace_1908151 : CollatzResearch.WordTrace tailWord_1908151 prefixEnd_1908151 979798624357469084137079 := by
  unfold tailWord_1908151
  simp only [CollatzResearch.WordTrace]
  refine ⟨69595984510102288090780307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46397323006734858727186871 69595984510102288090780307)
  ·
    refine ⟨104393976765153432136170461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69595984510102288090780307 104393976765153432136170461)
    ·
      refine ⟨39147741286932537051063923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104393976765153432136170461 39147741286932537051063923)
      ·
        refine ⟨58721611930398805576595885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39147741286932537051063923 58721611930398805576595885)
        ·
          refine ⟨22020604473899552091223457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58721611930398805576595885 22020604473899552091223457)
          ·
            refine ⟨16515453355424664068417593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22020604473899552091223457 16515453355424664068417593)
            ·
              refine ⟨12386590016568498051313195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16515453355424664068417593 12386590016568498051313195)
              ·
                refine ⟨18579885024852747076969793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386590016568498051313195 18579885024852747076969793)
                ·
                  refine ⟨13934913768639560307727345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18579885024852747076969793 13934913768639560307727345)
                  ·
                    refine ⟨10451185326479670230795509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13934913768639560307727345 10451185326479670230795509)
                    ·
                      refine ⟨979798624357469084137079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10451185326479670230795509 979798624357469084137079)
                      ·
                        rfl

theorem cell23_1908151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1908151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908151 prefixEnd_1908151 := by exact prefixLift 1908151
  have htrace : WordTrace (prefixWord ++ tailWord_1908151) baseStart_1908151 baseEnd_1908151 := by
    simpa [prefixWord, tailWord_1908151, baseEnd_1908151] using wordTrace_append hprefix tailTrace_1908151
  have hstable : (prefixWord ++ tailWord_1908151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908151).length < 2 ^ (prefixWord ++ tailWord_1908151).sum := by decide
  have hdescent : baseEnd_1908151 < baseStart_1908151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908156 : List Nat := [2, 2, 2, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1908156 : Nat := 118140960795 + 1908156 * 2 ^ 59
def prefixEnd_1908156 : Nat := 4983230072969 + 3 ^ 40 * 1908156 * 2
def baseEnd_1908156 : Nat := 979801191760741564574557

theorem tailTrace_1908156 : CollatzResearch.WordTrace tailWord_1908156 prefixEnd_1908156 979801191760741564574557 := by
  unfold tailWord_1908156
  simp only [CollatzResearch.WordTrace]
  refine ⟨34798083437542086972356161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46397444583389449296474881 34798083437542086972356161)
  ·
    refine ⟨26098562578156565229267121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34798083437542086972356161 26098562578156565229267121)
    ·
      refine ⟨19573921933617423921950341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26098562578156565229267121 19573921933617423921950341)
      ·
        refine ⟨3670110362553266985365689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19573921933617423921950341 3670110362553266985365689)
        ·
          refine ⟨2752582771914950239024267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3670110362553266985365689 2752582771914950239024267)
          ·
            refine ⟨4128874157872425358536401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752582771914950239024267 4128874157872425358536401)
            ·
              refine ⟨3096655618404319018902301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128874157872425358536401 3096655618404319018902301)
              ·
                refine ⟨1161245856901619632088363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3096655618404319018902301 1161245856901619632088363)
                ·
                  refine ⟨1741868785352429448132545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161245856901619632088363 1741868785352429448132545)
                  ·
                    refine ⟨1306401589014322086099409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1741868785352429448132545 1306401589014322086099409)
                    ·
                      refine ⟨979801191760741564574557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306401589014322086099409 979801191760741564574557)
                      ·
                        rfl

theorem cell23_1908156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1908156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908156 prefixEnd_1908156 := by exact prefixLift 1908156
  have htrace : WordTrace (prefixWord ++ tailWord_1908156) baseStart_1908156 baseEnd_1908156 := by
    simpa [prefixWord, tailWord_1908156, baseEnd_1908156] using wordTrace_append hprefix tailTrace_1908156
  have hstable : (prefixWord ++ tailWord_1908156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908156).length < 2 ^ (prefixWord ++ tailWord_1908156).sum := by decide
  have hdescent : baseEnd_1908156 < baseStart_1908156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908171 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 2, 6]
def baseStart_1908171 : Nat := 118140960795 + 1908171 * 2 ^ 59
def prefixEnd_1908171 : Nat := 4983230072969 + 3 ^ 40 * 1908171 * 2
def baseEnd_1908171 : Nat := 326602964656853001962329

theorem tailTrace_1908171 : CollatzResearch.WordTrace tailWord_1908171 prefixEnd_1908171 326602964656853001962329 := by
  unfold tailWord_1908171
  simp only [CollatzResearch.WordTrace]
  refine ⟨69596713970029831506508367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46397809313353221004338911 69596713970029831506508367)
  ·
    refine ⟨104395070955044747259762551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69596713970029831506508367 104395070955044747259762551)
    ·
      refine ⟨156592606432567120889643827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104395070955044747259762551 156592606432567120889643827)
      ·
        refine ⟨234888909648850681334465741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156592606432567120889643827 234888909648850681334465741)
        ·
          refine ⟨88083341118319005500424653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234888909648850681334465741 88083341118319005500424653)
          ·
            refine ⟨33031252919369627062659245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88083341118319005500424653 33031252919369627062659245)
            ·
              refine ⟨12386719844763610148497217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33031252919369627062659245 12386719844763610148497217)
              ·
                refine ⟨9290039883572707611372913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386719844763610148497217 9290039883572707611372913)
                ·
                  refine ⟨6967529912679530708529685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290039883572707611372913 6967529912679530708529685)
                  ·
                    refine ⟨326602964656853001962329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6967529912679530708529685 326602964656853001962329)
                    ·
                      rfl

theorem cell23_1908171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 6].length) (baseStart_1908171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908171 prefixEnd_1908171 := by exact prefixLift 1908171
  have htrace : WordTrace (prefixWord ++ tailWord_1908171) baseStart_1908171 baseEnd_1908171 := by
    simpa [prefixWord, tailWord_1908171, baseEnd_1908171] using wordTrace_append hprefix tailTrace_1908171
  have hstable : (prefixWord ++ tailWord_1908171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908171).length < 2 ^ (prefixWord ++ tailWord_1908171).sum := by decide
  have hdescent : baseEnd_1908171 < baseStart_1908171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908172 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1908172 : Nat := 118140960795 + 1908172 * 2 ^ 59
def prefixEnd_1908172 : Nat := 4983230072969 + 3 ^ 40 * 1908172 * 2
def baseEnd_1908172 : Nat := 979809407451213501974483

theorem tailTrace_1908172 : CollatzResearch.WordTrace tailWord_1908172 prefixEnd_1908172 979809407451213501974483 := by
  unfold tailWord_1908172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34798375221513104338647385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46397833628684139118196513 34798375221513104338647385)
  ·
    refine ⟨26098781416134828253985539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34798375221513104338647385 26098781416134828253985539)
    ·
      refine ⟨39148172124202242380978309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26098781416134828253985539 39148172124202242380978309)
      ·
        refine ⟨7340282273287920446433433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39148172124202242380978309 7340282273287920446433433)
        ·
          refine ⟨5505211704965940334825075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7340282273287920446433433 5505211704965940334825075)
          ·
            refine ⟨8257817557448910502237613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505211704965940334825075 8257817557448910502237613)
            ·
              refine ⟨3096681584043341438339105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8257817557448910502237613 3096681584043341438339105)
              ·
                refine ⟨2322511188032506078754329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096681584043341438339105 2322511188032506078754329)
                ·
                  refine ⟨1741883391024379559065747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322511188032506078754329 1741883391024379559065747)
                  ·
                    refine ⟨2612825086536569338598621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741883391024379559065747 2612825086536569338598621)
                    ·
                      refine ⟨979809407451213501974483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612825086536569338598621 979809407451213501974483)
                      ·
                        rfl

theorem cell23_1908172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1908172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908172 prefixEnd_1908172 := by exact prefixLift 1908172
  have htrace : WordTrace (prefixWord ++ tailWord_1908172) baseStart_1908172 baseEnd_1908172 := by
    simpa [prefixWord, tailWord_1908172, baseEnd_1908172] using wordTrace_append hprefix tailTrace_1908172
  have hstable : (prefixWord ++ tailWord_1908172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908172).length < 2 ^ (prefixWord ++ tailWord_1908172).sum := by decide
  have hdescent : baseEnd_1908172 < baseStart_1908172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908189 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1908189 : Nat := 118140960795 + 1908189 * 2 ^ 59
def prefixEnd_1908189 : Nat := 4983230072969 + 3 ^ 40 * 1908189 * 2
def baseEnd_1908189 : Nat := 979818136622339935461905

theorem tailTrace_1908189 : CollatzResearch.WordTrace tailWord_1908189 prefixEnd_1908189 979818136622339935461905 := by
  unfold tailWord_1908189
  simp only [CollatzResearch.WordTrace]
  refine ⟨69597370483964620580663621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46398246989309747053775747 69597370483964620580663621)
  ·
    refine ⟨13049506965743366358874429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69597370483964620580663621 13049506965743366358874429)
    ·
      refine ⟨4893565112153762384577911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13049506965743366358874429 4893565112153762384577911)
      ·
        refine ⟨7340347668230643576866867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4893565112153762384577911 7340347668230643576866867)
        ·
          refine ⟨11010521502345965365300301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7340347668230643576866867 11010521502345965365300301)
          ·
            refine ⟨4128945563379737011987613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11010521502345965365300301 4128945563379737011987613)
            ·
              refine ⟨1548354586267401379495355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4128945563379737011987613 1548354586267401379495355)
              ·
                refine ⟨2322531879401102069243033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548354586267401379495355 2322531879401102069243033)
                ·
                  refine ⟨1741898909550826551932275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322531879401102069243033 1741898909550826551932275)
                  ·
                    refine ⟨2612848364326239827898413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741898909550826551932275 2612848364326239827898413)
                    ·
                      refine ⟨979818136622339935461905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612848364326239827898413 979818136622339935461905)
                      ·
                        rfl

theorem cell23_1908189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1908189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908189 prefixEnd_1908189 := by exact prefixLift 1908189
  have htrace : WordTrace (prefixWord ++ tailWord_1908189) baseStart_1908189 baseEnd_1908189 := by
    simpa [prefixWord, tailWord_1908189, baseEnd_1908189] using wordTrace_append hprefix tailTrace_1908189
  have hstable : (prefixWord ++ tailWord_1908189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908189).length < 2 ^ (prefixWord ++ tailWord_1908189).sum := by decide
  have hdescent : baseEnd_1908189 < baseStart_1908189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908235 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 7]
def baseStart_1908235 : Nat := 118140960795 + 1908235 * 2 ^ 59
def prefixEnd_1908235 : Nat := 4983230072969 + 3 ^ 40 * 1908235 * 2
def baseEnd_1908235 : Nat := 108871306303605195054077

theorem tailTrace_1908235 : CollatzResearch.WordTrace tailWord_1908235 prefixEnd_1908235 108871306303605195054077 := by
  unfold tailWord_1908235
  simp only [CollatzResearch.WordTrace]
  refine ⟨69599048241797970436838159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46399365494531980291225439 69599048241797970436838159)
  ·
    refine ⟨104398572362696955655257239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69599048241797970436838159 104398572362696955655257239)
    ·
      refine ⟨156597858544045433482885859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104398572362696955655257239 156597858544045433482885859)
      ·
        refine ⟨234896787816068150224328789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156597858544045433482885859 234896787816068150224328789)
        ·
          refine ⟨2752696732219548635441353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 234896787816068150224328789 2752696732219548635441353)
          ·
            refine ⟨2064522549164661476581015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2752696732219548635441353 2064522549164661476581015)
            ·
              refine ⟨3096783823746992214871523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064522549164661476581015 3096783823746992214871523)
              ·
                refine ⟨4645175735620488322307285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096783823746992214871523 4645175735620488322307285)
                ·
                  refine ⟨108871306303605195054077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4645175735620488322307285 108871306303605195054077)
                  ·
                    rfl

theorem cell23_1908235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 7].length) (baseStart_1908235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908235 prefixEnd_1908235 := by exact prefixLift 1908235
  have htrace : WordTrace (prefixWord ++ tailWord_1908235) baseStart_1908235 baseEnd_1908235 := by
    simpa [prefixWord, tailWord_1908235, baseEnd_1908235] using wordTrace_append hprefix tailTrace_1908235
  have hstable : (prefixWord ++ tailWord_1908235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908235).length < 2 ^ (prefixWord ++ tailWord_1908235).sum := by decide
  have hdescent : baseEnd_1908235 < baseStart_1908235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908271 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_1908271 : Nat := 118140960795 + 1908271 * 2 ^ 59
def prefixEnd_1908271 : Nat := 4983230072969 + 3 ^ 40 * 1908271 * 2
def baseEnd_1908271 : Nat := 979860242036008614636527

theorem tailTrace_1908271 : CollatzResearch.WordTrace tailWord_1908271 prefixEnd_1908271 979860242036008614636527 := by
  unfold tailWord_1908271
  simp only [CollatzResearch.WordTrace]
  refine ⟨69600361269667548585148667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46400240846445032390099111 69600361269667548585148667)
  ·
    refine ⟨104400541904501322877723001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69600361269667548585148667 104400541904501322877723001)
    ·
      refine ⟨78300406428375992158292251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104400541904501322877723001 78300406428375992158292251)
      ·
        refine ⟨117450609642563988237438377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78300406428375992158292251 117450609642563988237438377)
        ·
          refine ⟨88087957231922991178078783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117450609642563988237438377 88087957231922991178078783)
          ·
            refine ⟨132131935847884486767118175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88087957231922991178078783 132131935847884486767118175)
            ·
              refine ⟨198197903771826730150677263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132131935847884486767118175 198197903771826730150677263)
              ·
                refine ⟨297296855657740095226015895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198197903771826730150677263 297296855657740095226015895)
                ·
                  refine ⟨445945283486610142839023843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297296855657740095226015895 445945283486610142839023843)
                  ·
                    refine ⟨668917925229915214258535765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445945283486610142839023843 668917925229915214258535765)
                    ·
                      refine ⟨979860242036008614636527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 668917925229915214258535765 979860242036008614636527)
                      ·
                        rfl

theorem cell23_1908271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_1908271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908271 prefixEnd_1908271 := by exact prefixLift 1908271
  have htrace : WordTrace (prefixWord ++ tailWord_1908271) baseStart_1908271 baseEnd_1908271 := by
    simpa [prefixWord, tailWord_1908271, baseEnd_1908271] using wordTrace_append hprefix tailTrace_1908271
  have hstable : (prefixWord ++ tailWord_1908271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908271).length < 2 ^ (prefixWord ++ tailWord_1908271).sum := by decide
  have hdescent : baseEnd_1908271 < baseStart_1908271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908288 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3]
def baseStart_1908288 : Nat := 118140960795 + 1908288 * 2 ^ 59
def prefixEnd_1908288 : Nat := 4983230072969 + 3 ^ 40 * 1908288 * 2
def baseEnd_1908288 : Nat := 979868971207135048123949

theorem tailTrace_1908288 : CollatzResearch.WordTrace tailWord_1908288 prefixEnd_1908288 979868971207135048123949 := by
  unfold tailWord_1908288
  simp only [CollatzResearch.WordTrace]
  refine ⟨34800490655302980244258759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46400654207070640325678345 34800490655302980244258759)
  ·
    refine ⟨52200735982954470366388139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34800490655302980244258759 52200735982954470366388139)
    ·
      refine ⟨78301103974431705549582209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52200735982954470366388139 78301103974431705549582209)
      ·
        refine ⟨58725827980823779162186657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78301103974431705549582209 58725827980823779162186657)
        ·
          refine ⟨44044370985617834371639993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58725827980823779162186657 44044370985617834371639993)
          ·
            refine ⟨33033278239213375778729995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44044370985617834371639993 33033278239213375778729995)
            ·
              refine ⟨49549917358820063668094993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33033278239213375778729995 49549917358820063668094993)
              ·
                refine ⟨37162438019115047751071245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49549917358820063668094993 37162438019115047751071245)
                ·
                  refine ⟨13935914257168142906651717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37162438019115047751071245 13935914257168142906651717)
                  ·
                    refine ⟨2612983923219026794997197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13935914257168142906651717 2612983923219026794997197)
                    ·
                      refine ⟨979868971207135048123949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2612983923219026794997197 979868971207135048123949)
                      ·
                        rfl

theorem cell23_1908288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_1908288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908288 prefixEnd_1908288 := by exact prefixLift 1908288
  have htrace : WordTrace (prefixWord ++ tailWord_1908288) baseStart_1908288 baseEnd_1908288 := by
    simpa [prefixWord, tailWord_1908288, baseEnd_1908288] using wordTrace_append hprefix tailTrace_1908288
  have hstable : (prefixWord ++ tailWord_1908288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908288).length < 2 ^ (prefixWord ++ tailWord_1908288).sum := by decide
  have hdescent : baseEnd_1908288 < baseStart_1908288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908335 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 3]
def baseStart_1908335 : Nat := 118140960795 + 1908335 * 2 ^ 59
def prefixEnd_1908335 : Nat := 4983230072969 + 3 ^ 40 * 1908335 * 2
def baseEnd_1908335 : Nat := 979893104797896364236233

theorem tailTrace_1908335 : CollatzResearch.WordTrace tailWord_1908335 prefixEnd_1908335 979893104797896364236233 := by
  unfold tailWord_1908335
  simp only [CollatzResearch.WordTrace]
  refine ⟨69602695541435687515478459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46401797027623791676985639 69602695541435687515478459)
  ·
    refine ⟨104404043312153531273217689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69602695541435687515478459 104404043312153531273217689)
    ·
      refine ⟨78303032484115148454913267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104404043312153531273217689 78303032484115148454913267)
      ·
        refine ⟨117454548726172722682369901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78303032484115148454913267 117454548726172722682369901)
        ·
          refine ⟨44045455772314771005888713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117454548726172722682369901 44045455772314771005888713)
          ·
            refine ⟨33034091829236078254416535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44045455772314771005888713 33034091829236078254416535)
            ·
              refine ⟨49551137743854117381624803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33034091829236078254416535 49551137743854117381624803)
              ·
                refine ⟨74326706615781176072437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49551137743854117381624803 74326706615781176072437205)
                ·
                  refine ⟨1742032186307371314197747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74326706615781176072437205 1742032186307371314197747)
                  ·
                    refine ⟨2613048279461056971296621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1742032186307371314197747 2613048279461056971296621)
                    ·
                      refine ⟨979893104797896364236233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613048279461056971296621 979893104797896364236233)
                      ·
                        rfl

theorem cell23_1908335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 3].length) (baseStart_1908335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908335 prefixEnd_1908335 := by exact prefixLift 1908335
  have htrace : WordTrace (prefixWord ++ tailWord_1908335) baseStart_1908335 baseEnd_1908335 := by
    simpa [prefixWord, tailWord_1908335, baseEnd_1908335] using wordTrace_append hprefix tailTrace_1908335
  have hstable : (prefixWord ++ tailWord_1908335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908335).length < 2 ^ (prefixWord ++ tailWord_1908335).sum := by decide
  have hdescent : baseEnd_1908335 < baseStart_1908335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908342 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1908342 : Nat := 118140960795 + 1908342 * 2 ^ 59
def prefixEnd_1908342 : Nat := 4983230072969 + 3 ^ 40 * 1908342 * 2
def baseEnd_1908342 : Nat := 108877411018053092983189

theorem tailTrace_1908342 : CollatzResearch.WordTrace tailWord_1908342 prefixEnd_1908342 108877411018053092983189 := by
  unfold tailWord_1908342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350184428275645481936455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46401967234940218473988853 4350184428275645481936455)
  ·
    refine ⟨6525276642413468222904683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4350184428275645481936455 6525276642413468222904683)
    ·
      refine ⟨9787914963620202334357025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6525276642413468222904683 9787914963620202334357025)
      ·
        refine ⟨7340936222715151750767769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9787914963620202334357025 7340936222715151750767769)
        ·
          refine ⟨5505702167036363813075827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7340936222715151750767769 5505702167036363813075827)
          ·
            refine ⟨8258553250554545719613741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505702167036363813075827 8258553250554545719613741)
            ·
              refine ⟨3096957468957954644855153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8258553250554545719613741 3096957468957954644855153)
              ·
                refine ⟨2322718101718465983641365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096957468957954644855153 2322718101718465983641365)
                ·
                  refine ⟨108877411018053092983189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2322718101718465983641365 108877411018053092983189)
                  ·
                    rfl

theorem cell23_1908342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1908342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908342 prefixEnd_1908342 := by exact prefixLift 1908342
  have htrace : WordTrace (prefixWord ++ tailWord_1908342) baseStart_1908342 baseEnd_1908342 := by
    simpa [prefixWord, tailWord_1908342, baseEnd_1908342] using wordTrace_append hprefix tailTrace_1908342
  have hstable : (prefixWord ++ tailWord_1908342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908342).length < 2 ^ (prefixWord ++ tailWord_1908342).sum := by decide
  have hdescent : baseEnd_1908342 < baseStart_1908342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908352 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 3, 1, 3]
def baseStart_1908352 : Nat := 118140960795 + 1908352 * 2 ^ 59
def prefixEnd_1908352 : Nat := 4983230072969 + 3 ^ 40 * 1908352 * 2
def baseEnd_1908352 : Nat := 979901833969022797723655

theorem tailTrace_1908352 : CollatzResearch.WordTrace tailWord_1908352 prefixEnd_1908352 979901833969022797723655 := by
  unfold tailWord_1908352
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801657791187049709423655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46402210388249399612564873 34801657791187049709423655)
  ·
    refine ⟨52202486686780574564135483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34801657791187049709423655 52202486686780574564135483)
    ·
      refine ⟨78303730030170861846203225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52202486686780574564135483 78303730030170861846203225)
      ·
        refine ⟨58727797522628146384652419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78303730030170861846203225 58727797522628146384652419)
        ·
          refine ⟨88091696283942219576978629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58727797522628146384652419 88091696283942219576978629)
          ·
            refine ⟨16517193053239166170683493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88091696283942219576978629 16517193053239166170683493)
            ·
              refine ⟨3096973697482343657003155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16517193053239166170683493 3096973697482343657003155)
              ·
                refine ⟨4645460546223515485504733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096973697482343657003155 4645460546223515485504733)
                ·
                  refine ⟨1742047704833818307064275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4645460546223515485504733 1742047704833818307064275)
                  ·
                    refine ⟨2613071557250727460596413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1742047704833818307064275 2613071557250727460596413)
                    ·
                      refine ⟨979901833969022797723655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613071557250727460596413 979901833969022797723655)
                      ·
                        rfl

theorem cell23_1908352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_1908352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908352 prefixEnd_1908352 := by exact prefixLift 1908352
  have htrace : WordTrace (prefixWord ++ tailWord_1908352) baseStart_1908352 baseEnd_1908352 := by
    simpa [prefixWord, tailWord_1908352, baseEnd_1908352] using wordTrace_append hprefix tailTrace_1908352
  have hstable : (prefixWord ++ tailWord_1908352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908352).length < 2 ^ (prefixWord ++ tailWord_1908352).sum := by decide
  have hdescent : baseEnd_1908352 < baseStart_1908352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908362 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_1908362 : Nat := 118140960795 + 1908362 * 2 ^ 59
def prefixEnd_1908362 : Nat := 4983230072969 + 3 ^ 40 * 1908362 * 2
def baseEnd_1908362 : Nat := 979906968775567758598609

theorem tailTrace_1908362 : CollatzResearch.WordTrace tailWord_1908362 prefixEnd_1908362 979906968775567758598609 := by
  unfold tailWord_1908362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17400920078084467781677835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46402453541558580751140893 17400920078084467781677835)
  ·
    refine ⟨26101380117126701672516753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17400920078084467781677835 26101380117126701672516753)
    ·
      refine ⟨19576035087845026254387565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26101380117126701672516753 19576035087845026254387565)
      ·
        refine ⟨7341013157941884845395337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19576035087845026254387565 7341013157941884845395337)
        ·
          refine ⟨5505759868456413634046503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7341013157941884845395337 5505759868456413634046503)
          ·
            refine ⟨8258639802684620451069755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505759868456413634046503 8258639802684620451069755)
            ·
              refine ⟨12387959704026930676604633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8258639802684620451069755 12387959704026930676604633)
              ·
                refine ⟨9290969778020198007453475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12387959704026930676604633 9290969778020198007453475)
                ·
                  refine ⟨13936454667030297011180213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9290969778020198007453475 13936454667030297011180213)
                  ·
                    refine ⟨1306542625034090344798145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13936454667030297011180213 1306542625034090344798145)
                    ·
                      refine ⟨979906968775567758598609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306542625034090344798145 979906968775567758598609)
                      ·
                        rfl

theorem cell23_1908362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_1908362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908362 prefixEnd_1908362 := by exact prefixLift 1908362
  have htrace : WordTrace (prefixWord ++ tailWord_1908362) baseStart_1908362 baseEnd_1908362 := by
    simpa [prefixWord, tailWord_1908362, baseEnd_1908362] using wordTrace_append hprefix tailTrace_1908362
  have hstable : (prefixWord ++ tailWord_1908362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908362).length < 2 ^ (prefixWord ++ tailWord_1908362).sum := by decide
  have hdescent : baseEnd_1908362 < baseStart_1908362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908409 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 3, 2, 2]
def baseStart_1908409 : Nat := 118140960795 + 1908409 * 2 ^ 59
def prefixEnd_1908409 : Nat := 4983230072969 + 3 ^ 40 * 1908409 * 2
def baseEnd_1908409 : Nat := 979931102366329074710893

theorem tailTrace_1908409 : CollatzResearch.WordTrace tailWord_1908409 prefixEnd_1908409 979931102366329074710893 := by
  unfold tailWord_1908409
  simp only [CollatzResearch.WordTrace]
  refine ⟨69605394543167598153672281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46403596362111732102448187 69605394543167598153672281)
  ·
    refine ⟨52204045907375698615254211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69605394543167598153672281 52204045907375698615254211)
    ·
      refine ⟨78306068861063547922881317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52204045907375698615254211 78306068861063547922881317)
      ·
        refine ⟨14682387911449415235540247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78306068861063547922881317 14682387911449415235540247)
        ·
          refine ⟨22023581867174122853310371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14682387911449415235540247 22023581867174122853310371)
          ·
            refine ⟨33035372800761184279965557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22023581867174122853310371 33035372800761184279965557)
            ·
              refine ⟨3097066200071361026246771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33035372800761184279965557 3097066200071361026246771)
              ·
                refine ⟨4645599300107041539370157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097066200071361026246771 4645599300107041539370157)
                ·
                  refine ⟨1742099737540140577263809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4645599300107041539370157 1742099737540140577263809)
                  ·
                    refine ⟨1306574803155105432947857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1742099737540140577263809 1306574803155105432947857)
                    ·
                      refine ⟨979931102366329074710893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306574803155105432947857 979931102366329074710893)
                      ·
                        rfl

theorem cell23_1908409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_1908409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908409 prefixEnd_1908409 := by exact prefixLift 1908409
  have htrace : WordTrace (prefixWord ++ tailWord_1908409) baseStart_1908409 baseEnd_1908409 := by
    simpa [prefixWord, tailWord_1908409, baseEnd_1908409] using wordTrace_append hprefix tailTrace_1908409
  have hstable : (prefixWord ++ tailWord_1908409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908409).length < 2 ^ (prefixWord ++ tailWord_1908409).sum := by decide
  have hdescent : baseEnd_1908409 < baseStart_1908409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908426 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_1908426 : Nat := 118140960795 + 1908426 * 2 ^ 59
def prefixEnd_1908426 : Nat := 4983230072969 + 3 ^ 40 * 1908426 * 2
def baseEnd_1908426 : Nat := 979939831537455508198315

theorem tailTrace_1908426 : CollatzResearch.WordTrace tailWord_1908426 prefixEnd_1908426 979939831537455508198315 := by
  unfold tailWord_1908426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17401503646026502514260283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46404009722737340038027421 17401503646026502514260283)
  ·
    refine ⟨26102255469039753771390425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17401503646026502514260283 26102255469039753771390425)
    ·
      refine ⟨19576691601779815328542819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26102255469039753771390425 19576691601779815328542819)
      ·
        refine ⟨29365037402669722992814229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19576691601779815328542819 29365037402669722992814229)
        ·
          refine ⟨1376486128250143265288167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29365037402669722992814229 1376486128250143265288167)
          ·
            refine ⟨2064729192375214897932251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376486128250143265288167 2064729192375214897932251)
            ·
              refine ⟨3097093788562822346898377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064729192375214897932251 3097093788562822346898377)
              ·
                refine ⟨2322820341422116760173783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3097093788562822346898377 2322820341422116760173783)
                ·
                  refine ⟨3484230512133175140260675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322820341422116760173783 3484230512133175140260675)
                  ·
                    refine ⟨5226345768199762710391013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3484230512133175140260675 5226345768199762710391013)
                    ·
                      refine ⟨979939831537455508198315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5226345768199762710391013 979939831537455508198315)
                      ·
                        rfl

theorem cell23_1908426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_1908426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908426 prefixEnd_1908426 := by exact prefixLift 1908426
  have htrace : WordTrace (prefixWord ++ tailWord_1908426) baseStart_1908426 baseEnd_1908426 := by
    simpa [prefixWord, tailWord_1908426, baseEnd_1908426] using wordTrace_append hprefix tailTrace_1908426
  have hstable : (prefixWord ++ tailWord_1908426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908426).length < 2 ^ (prefixWord ++ tailWord_1908426).sum := by decide
  have hdescent : baseEnd_1908426 < baseStart_1908426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908442 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_1908442 : Nat := 118140960795 + 1908442 * 2 ^ 59
def prefixEnd_1908442 : Nat := 4983230072969 + 3 ^ 40 * 1908442 * 2
def baseEnd_1908442 : Nat := 979948047227927445598241

theorem tailTrace_1908442 : CollatzResearch.WordTrace tailWord_1908442 prefixEnd_1908442 979948047227927445598241 := by
  unfold tailWord_1908442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17401649538012011197405895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46404398768032029859749053 17401649538012011197405895)
  ·
    refine ⟨26102474307018016796108843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17401649538012011197405895 26102474307018016796108843)
    ·
      refine ⟨39153711460527025194163265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26102474307018016796108843 39153711460527025194163265)
      ·
        refine ⟨29365283595395268895622449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39153711460527025194163265 29365283595395268895622449)
        ·
          refine ⟨22023962696546451671716837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29365283595395268895622449 22023962696546451671716837)
          ·
            refine ⟨4129493005602459688446907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22023962696546451671716837 4129493005602459688446907)
            ·
              refine ⟨6194239508403689532670361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129493005602459688446907 6194239508403689532670361)
              ·
                refine ⟨4645679631302767149502771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194239508403689532670361 4645679631302767149502771)
                ·
                  refine ⟨6968519446954150724254157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645679631302767149502771 6968519446954150724254157)
                  ·
                    refine ⟨2613194792607806521595309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6968519446954150724254157 2613194792607806521595309)
                    ·
                      refine ⟨979948047227927445598241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613194792607806521595309 979948047227927445598241)
                      ·
                        rfl

theorem cell23_1908442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_1908442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908442 prefixEnd_1908442 := by exact prefixLift 1908442
  have htrace : WordTrace (prefixWord ++ tailWord_1908442) baseStart_1908442 baseEnd_1908442 := by
    simpa [prefixWord, tailWord_1908442, baseEnd_1908442] using wordTrace_append hprefix tailTrace_1908442
  have hstable : (prefixWord ++ tailWord_1908442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908442).length < 2 ^ (prefixWord ++ tailWord_1908442).sum := by decide
  have hdescent : baseEnd_1908442 < baseStart_1908442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908465 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1908465 : Nat := 118140960795 + 1908465 * 2 ^ 59
def prefixEnd_1908465 : Nat := 4983230072969 + 3 ^ 40 * 1908465 * 2
def baseEnd_1908465 : Nat := 979959857282980855610635

theorem tailTrace_1908465 : CollatzResearch.WordTrace tailWord_1908465 prefixEnd_1908465 979959857282980855610635 := by
  unfold tailWord_1908465
  simp only [CollatzResearch.WordTrace]
  refine ⟨69607437030964719717710849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46404958020643146478473899 69607437030964719717710849)
  ·
    refine ⟨52205577773223539788283137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69607437030964719717710849 52205577773223539788283137)
    ·
      refine ⟨39154183329917654841212353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52205577773223539788283137 39154183329917654841212353)
      ·
        refine ⟨29365637497438241130909265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39154183329917654841212353 29365637497438241130909265)
        ·
          refine ⟨22024228123078680848181949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29365637497438241130909265 22024228123078680848181949)
          ·
            refine ⟨8259085546154505318068231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22024228123078680848181949 8259085546154505318068231)
            ·
              refine ⟨12388628319231757977102347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259085546154505318068231 12388628319231757977102347)
              ·
                refine ⟨18582942478847636965653521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12388628319231757977102347 18582942478847636965653521)
                ·
                  refine ⟨13937206859135727724240141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18582942478847636965653521 13937206859135727724240141)
                  ·
                    refine ⟨5226452572175897896590053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13937206859135727724240141 5226452572175897896590053)
                    ·
                      refine ⟨979959857282980855610635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5226452572175897896590053 979959857282980855610635)
                      ·
                        rfl

theorem cell23_1908465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1908465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908465 prefixEnd_1908465 := by exact prefixLift 1908465
  have htrace : WordTrace (prefixWord ++ tailWord_1908465) baseStart_1908465 baseEnd_1908465 := by
    simpa [prefixWord, tailWord_1908465, baseEnd_1908465] using wordTrace_append hprefix tailTrace_1908465
  have hstable : (prefixWord ++ tailWord_1908465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908465).length < 2 ^ (prefixWord ++ tailWord_1908465).sum := by decide
  have hdescent : baseEnd_1908465 < baseStart_1908465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908482 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1908482 : Nat := 118140960795 + 1908482 * 2 ^ 59
def prefixEnd_1908482 : Nat := 4983230072969 + 3 ^ 40 * 1908482 * 2
def baseEnd_1908482 : Nat := 979968586454107289098057

theorem tailTrace_1908482 : CollatzResearch.WordTrace tailWord_1908482 prefixEnd_1908482 979968586454107289098057 := by
  unfold tailWord_1908482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402014267975782905269925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46405371381268754414053133 17402014267975782905269925)
  ·
    refine ⟨3262877675245459294738111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17402014267975782905269925 3262877675245459294738111)
    ·
      refine ⟨4894316512868188942107167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262877675245459294738111 4894316512868188942107167)
      ·
        refine ⟨7341474769302283413160751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4894316512868188942107167 7341474769302283413160751)
        ·
          refine ⟨11012212153953425119741127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341474769302283413160751 11012212153953425119741127)
          ·
            refine ⟨16518318230930137679611691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11012212153953425119741127 16518318230930137679611691)
            ·
              refine ⟨24777477346395206519417537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16518318230930137679611691 24777477346395206519417537)
              ·
                refine ⟨18583108009796404889563153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24777477346395206519417537 18583108009796404889563153)
                ·
                  refine ⟨13937331007347303667172365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18583108009796404889563153 13937331007347303667172365)
                  ·
                    refine ⟨5226499127755238875189637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13937331007347303667172365 5226499127755238875189637)
                    ·
                      refine ⟨979968586454107289098057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5226499127755238875189637 979968586454107289098057)
                      ·
                        rfl

theorem cell23_1908482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1908482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908482 prefixEnd_1908482 := by exact prefixLift 1908482
  have htrace : WordTrace (prefixWord ++ tailWord_1908482) baseStart_1908482 baseEnd_1908482 := by
    simpa [prefixWord, tailWord_1908482, baseEnd_1908482] using wordTrace_append hprefix tailTrace_1908482
  have hstable : (prefixWord ++ tailWord_1908482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908482).length < 2 ^ (prefixWord ++ tailWord_1908482).sum := by decide
  have hdescent : baseEnd_1908482 < baseStart_1908482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908503 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1908503 : Nat := 118140960795 + 1908503 * 2 ^ 59
def prefixEnd_1908503 : Nat := 4983230072969 + 3 ^ 40 * 1908503 * 2
def baseEnd_1908503 : Nat := 979979369547851706935461

theorem tailTrace_1908503 : CollatzResearch.WordTrace tailWord_1908503 prefixEnd_1908503 979979369547851706935461 := by
  unfold tailWord_1908503
  simp only [CollatzResearch.WordTrace]
  refine ⟨69608823004827052207594163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46405882003218034805062775 69608823004827052207594163)
  ·
    refine ⟨104413234507240578311391245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69608823004827052207594163 104413234507240578311391245)
    ·
      refine ⟨39154962940215216866771717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104413234507240578311391245 39154962940215216866771717)
      ·
        refine ⟨7341555551290353162519697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39154962940215216866771717 7341555551290353162519697)
        ·
          refine ⟨5506166663467764871889773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7341555551290353162519697 5506166663467764871889773)
          ·
            refine ⟨2064812498800411826958665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5506166663467764871889773 2064812498800411826958665)
            ·
              refine ⟨1548609374100308870218999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064812498800411826958665 1548609374100308870218999)
              ·
                refine ⟨2322914061150463305328499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548609374100308870218999 2322914061150463305328499)
                ·
                  refine ⟨3484371091725694957992749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322914061150463305328499 3484371091725694957992749)
                  ·
                    refine ⟨1306639159397135609247281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484371091725694957992749 1306639159397135609247281)
                    ·
                      refine ⟨979979369547851706935461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306639159397135609247281 979979369547851706935461)
                      ·
                        rfl

theorem cell23_1908503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1908503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908503 prefixEnd_1908503 := by exact prefixLift 1908503
  have htrace : WordTrace (prefixWord ++ tailWord_1908503) baseStart_1908503 baseEnd_1908503 := by
    simpa [prefixWord, tailWord_1908503, baseEnd_1908503] using wordTrace_append hprefix tailTrace_1908503
  have hstable : (prefixWord ++ tailWord_1908503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908503).length < 2 ^ (prefixWord ++ tailWord_1908503).sum := by decide
  have hdescent : baseEnd_1908503 < baseStart_1908503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908516 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_1908516 : Nat := 118140960795 + 1908516 * 2 ^ 59
def prefixEnd_1908516 : Nat := 4983230072969 + 3 ^ 40 * 1908516 * 2
def baseEnd_1908516 : Nat := 979986044796360156072901

theorem tailTrace_1908516 : CollatzResearch.WordTrace tailWord_1908516 prefixEnd_1908516 979986044796360156072901 := by
  unfold tailWord_1908516
  simp only [CollatzResearch.WordTrace]
  refine ⟨34804648576889977713908701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46406198102519970285211601 34804648576889977713908701)
  ·
    refine ⟨13051743216333741642715763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34804648576889977713908701 13051743216333741642715763)
    ·
      refine ⟨19577614824500612464073645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13051743216333741642715763 19577614824500612464073645)
      ·
        refine ⟨7341605559187729674027617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19577614824500612464073645 7341605559187729674027617)
        ·
          refine ⟨5506204169390797255520713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7341605559187729674027617 5506204169390797255520713)
          ·
            refine ⟨4129653127043097941640535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5506204169390797255520713 4129653127043097941640535)
            ·
              refine ⟨6194479690564646912460803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129653127043097941640535 6194479690564646912460803)
              ·
                refine ⟨9291719535846970368691205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194479690564646912460803 9291719535846970368691205)
                ·
                  refine ⟨1742197412971306944129601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9291719535846970368691205 1742197412971306944129601)
                  ·
                    refine ⟨1306648059728480208097201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1742197412971306944129601 1306648059728480208097201)
                    ·
                      refine ⟨979986044796360156072901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306648059728480208097201 979986044796360156072901)
                      ·
                        rfl

theorem cell23_1908516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_1908516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908516 prefixEnd_1908516 := by exact prefixLift 1908516
  have htrace : WordTrace (prefixWord ++ tailWord_1908516) baseStart_1908516 baseEnd_1908516 := by
    simpa [prefixWord, tailWord_1908516, baseEnd_1908516] using wordTrace_append hprefix tailTrace_1908516
  have hstable : (prefixWord ++ tailWord_1908516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908516).length < 2 ^ (prefixWord ++ tailWord_1908516).sum := by decide
  have hdescent : baseEnd_1908516 < baseStart_1908516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908533 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_1908533 : Nat := 118140960795 + 1908533 * 2 ^ 59
def prefixEnd_1908533 : Nat := 4983230072969 + 3 ^ 40 * 1908533 * 2
def baseEnd_1908533 : Nat := 979994773967486589560323

theorem tailTrace_1908533 : CollatzResearch.WordTrace tailWord_1908533 prefixEnd_1908533 979994773967486589560323 := by
  unfold tailWord_1908533
  simp only [CollatzResearch.WordTrace]
  refine ⟨69609917194718367331186253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46406611463145578220790835 69609917194718367331186253)
  ·
    refine ⟨26103718948019387749194845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69609917194718367331186253 26103718948019387749194845)
    ·
      refine ⟨9788894605507270405948067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26103718948019387749194845 9788894605507270405948067)
      ·
        refine ⟨14683341908260905608922101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788894605507270405948067 14683341908260905608922101)
        ·
          refine ⟨1376563303899459900836447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14683341908260905608922101 1376563303899459900836447)
          ·
            refine ⟨2064844955849189851254671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376563303899459900836447 2064844955849189851254671)
            ·
              refine ⟨3097267433773784776882007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064844955849189851254671 3097267433773784776882007)
              ·
                refine ⟨4645901150660677165323011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097267433773784776882007 4645901150660677165323011)
                ·
                  refine ⟨6968851725991015747984517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645901150660677165323011 6968851725991015747984517)
                  ·
                    refine ⟨1306659698623315452747097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6968851725991015747984517 1306659698623315452747097)
                    ·
                      refine ⟨979994773967486589560323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306659698623315452747097 979994773967486589560323)
                      ·
                        rfl

theorem cell23_1908533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_1908533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908533 prefixEnd_1908533 := by exact prefixLift 1908533
  have htrace : WordTrace (prefixWord ++ tailWord_1908533) baseStart_1908533 baseEnd_1908533 := by
    simpa [prefixWord, tailWord_1908533, baseEnd_1908533] using wordTrace_append hprefix tailTrace_1908533
  have hstable : (prefixWord ++ tailWord_1908533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908533).length < 2 ^ (prefixWord ++ tailWord_1908533).sum := by decide
  have hdescent : baseEnd_1908533 < baseStart_1908533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908535 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 6, 5]
def baseStart_1908535 : Nat := 118140960795 + 1908535 * 2 ^ 59
def prefixEnd_1908535 : Nat := 4983230072969 + 3 ^ 40 * 1908535 * 2
def baseEnd_1908535 : Nat := 326665266976265193911771

theorem tailTrace_1908535 : CollatzResearch.WordTrace tailWord_1908535 prefixEnd_1908535 326665266976265193911771 := by
  unfold tailWord_1908535
  simp only [CollatzResearch.WordTrace]
  refine ⟨69609990140711121672759059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46406660093807414448506039 69609990140711121672759059)
  ·
    refine ⟨104414985211066682509138589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69609990140711121672759059 104414985211066682509138589)
    ·
      refine ⟨39155619454150005940926971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104414985211066682509138589 39155619454150005940926971)
      ·
        refine ⟨58733429181225008911390457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39155619454150005940926971 58733429181225008911390457)
        ·
          refine ⟨44050071885918756683542843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58733429181225008911390457 44050071885918756683542843)
          ·
            refine ⟨66075107828878135025314265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44050071885918756683542843 66075107828878135025314265)
            ·
              refine ⟨49556330871658601268985699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66075107828878135025314265 49556330871658601268985699)
              ·
                refine ⟨74334496307487901903478549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49556330871658601268985699 74334496307487901903478549)
                ·
                  refine ⟨3484429514413495401725557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74334496307487901903478549 3484429514413495401725557)
                  ·
                    refine ⟨326665266976265193911771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3484429514413495401725557 326665266976265193911771)
                    ·
                      rfl

theorem cell23_1908535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_1908535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908535 prefixEnd_1908535 := by exact prefixLift 1908535
  have htrace : WordTrace (prefixWord ++ tailWord_1908535) baseStart_1908535 baseEnd_1908535 := by
    simpa [prefixWord, tailWord_1908535, baseEnd_1908535] using wordTrace_append hprefix tailTrace_1908535
  have hstable : (prefixWord ++ tailWord_1908535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908535).length < 2 ^ (prefixWord ++ tailWord_1908535).sum := by decide
  have hdescent : baseEnd_1908535 < baseStart_1908535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908556 : List Nat := [2, 2, 1, 3, 4, 2, 1, 3, 5]
def baseStart_1908556 : Nat := 118140960795 + 1908556 * 2 ^ 59
def prefixEnd_1908556 : Nat := 4983230072969 + 3 ^ 40 * 1908556 * 2
def baseEnd_1908556 : Nat := 108889620446948888841413

theorem tailTrace_1908556 : CollatzResearch.WordTrace tailWord_1908556 prefixEnd_1908556 108889620446948888841413 := by
  unfold tailWord_1908556
  simp only [CollatzResearch.WordTrace]
  refine ⟨34805378036817521129636761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46407170715756694839515681 34805378036817521129636761)
  ·
    refine ⟨26104033527613140847227571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34805378036817521129636761 26104033527613140847227571)
    ·
      refine ⟨39156050291419711270841357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26104033527613140847227571 39156050291419711270841357)
      ·
        refine ⟨14683518859282391726565509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39156050291419711270841357 14683518859282391726565509)
        ·
          refine ⟨2753159786115448448731033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14683518859282391726565509 2753159786115448448731033)
          ·
            refine ⟨2064869839586586336548275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753159786115448448731033 2064869839586586336548275)
            ·
              refine ⟨3097304759379879504822413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064869839586586336548275 3097304759379879504822413)
              ·
                refine ⟨1161489284767454814308405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097304759379879504822413 1161489284767454814308405)
                ·
                  refine ⟨108889620446948888841413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161489284767454814308405 108889620446948888841413)
                  ·
                    rfl

theorem cell23_1908556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_1908556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908556 prefixEnd_1908556 := by exact prefixLift 1908556
  have htrace : WordTrace (prefixWord ++ tailWord_1908556) baseStart_1908556 baseEnd_1908556 := by
    simpa [prefixWord, tailWord_1908556, baseEnd_1908556] using wordTrace_append hprefix tailTrace_1908556
  have hstable : (prefixWord ++ tailWord_1908556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908556).length < 2 ^ (prefixWord ++ tailWord_1908556).sum := by decide
  have hdescent : baseEnd_1908556 < baseStart_1908556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908585 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_1908585 : Nat := 118140960795 + 1908585 * 2 ^ 59
def prefixEnd_1908585 : Nat := 4983230072969 + 3 ^ 40 * 1908585 * 2
def baseEnd_1908585 : Nat := 980021474961520386110083

theorem tailTrace_1908585 : CollatzResearch.WordTrace tailWord_1908585 prefixEnd_1908585 980021474961520386110083 := by
  unfold tailWord_1908585
  simp only [CollatzResearch.WordTrace]
  refine ⟨69611813790529980212079209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46407875860353320141386139 69611813790529980212079209)
  ·
    refine ⟨52208860342897485159059407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69611813790529980212079209 52208860342897485159059407)
    ·
      refine ⟨78313290514346227738589111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52208860342897485159059407 78313290514346227738589111)
      ·
        refine ⟨117469935771519341607883667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78313290514346227738589111 117469935771519341607883667)
        ·
          refine ⟨176204903657279012411825501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117469935771519341607883667 176204903657279012411825501)
          ·
            refine ⟨66076838871479629654434563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176204903657279012411825501 66076838871479629654434563)
            ·
              refine ⟨99115258307219444481651845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66076838871479629654434563 99115258307219444481651845)
              ·
                refine ⟨18584110932603645840309721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99115258307219444481651845 18584110932603645840309721)
                ·
                  refine ⟨13938083199452734380232291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18584110932603645840309721 13938083199452734380232291)
                  ·
                    refine ⟨20907124799179101570348437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13938083199452734380232291 20907124799179101570348437)
                    ·
                      refine ⟨980021474961520386110083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20907124799179101570348437 980021474961520386110083)
                      ·
                        rfl

theorem cell23_1908585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_1908585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908585 prefixEnd_1908585 := by exact prefixLift 1908585
  have htrace : WordTrace (prefixWord ++ tailWord_1908585) baseStart_1908585 baseEnd_1908585 := by
    simpa [prefixWord, tailWord_1908585, baseEnd_1908585] using wordTrace_append hprefix tailTrace_1908585
  have hstable : (prefixWord ++ tailWord_1908585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908585).length < 2 ^ (prefixWord ++ tailWord_1908585).sum := by decide
  have hdescent : baseEnd_1908585 < baseStart_1908585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908589 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_1908589 : Nat := 118140960795 + 1908589 * 2 ^ 59
def prefixEnd_1908589 : Nat := 4983230072969 + 3 ^ 40 * 1908589 * 2
def baseEnd_1908589 : Nat := 980023528884138370460065

theorem tailTrace_1908589 : CollatzResearch.WordTrace tailWord_1908589 prefixEnd_1908589 980023528884138370460065 := by
  unfold tailWord_1908589
  simp only [CollatzResearch.WordTrace]
  refine ⟨69611959682515488895224821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46407973121676992596816547 69611959682515488895224821)
  ·
    refine ⟨6526121220235827083927327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69611959682515488895224821 6526121220235827083927327)
    ·
      refine ⟨9789181830353740625890991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6526121220235827083927327 9789181830353740625890991)
      ·
        refine ⟨14683772745530610938836487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9789181830353740625890991 14683772745530610938836487)
        ·
          refine ⟨22025659118295916408254731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14683772745530610938836487 22025659118295916408254731)
          ·
            refine ⟨33038488677443874612382097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22025659118295916408254731 33038488677443874612382097)
            ·
              refine ⟨24778866508082905959286573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33038488677443874612382097 24778866508082905959286573)
              ·
                refine ⟨9292074940531089734732465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24778866508082905959286573 9292074940531089734732465)
                ·
                  refine ⟨6969056205398317301049349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9292074940531089734732465 6969056205398317301049349)
                  ·
                    refine ⟨1306698038512184493946753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969056205398317301049349 1306698038512184493946753)
                    ·
                      refine ⟨980023528884138370460065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306698038512184493946753 980023528884138370460065)
                      ·
                        rfl

theorem cell23_1908589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_1908589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908589 prefixEnd_1908589 := by exact prefixLift 1908589
  have htrace : WordTrace (prefixWord ++ tailWord_1908589) baseStart_1908589 baseEnd_1908589 := by
    simpa [prefixWord, tailWord_1908589, baseEnd_1908589] using wordTrace_append hprefix tailTrace_1908589
  have hstable : (prefixWord ++ tailWord_1908589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908589).length < 2 ^ (prefixWord ++ tailWord_1908589).sum := by decide
  have hdescent : baseEnd_1908589 < baseStart_1908589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908592 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3]
def baseStart_1908592 : Nat := 118140960795 + 1908592 * 2 ^ 59
def prefixEnd_1908592 : Nat := 4983230072969 + 3 ^ 40 * 1908592 * 2
def baseEnd_1908592 : Nat := 980025069326101858722551

theorem tailTrace_1908592 : CollatzResearch.WordTrace tailWord_1908592 prefixEnd_1908592 980025069326101858722551 := by
  unfold tailWord_1908592
  simp only [CollatzResearch.WordTrace]
  refine ⟨34806034550752310203792015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46408046067669746938389353 34806034550752310203792015)
  ·
    refine ⟨52209051826128465305688023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34806034550752310203792015 52209051826128465305688023)
    ·
      refine ⟨78313577739192697958532035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52209051826128465305688023 78313577739192697958532035)
      ·
        refine ⟨117470366608789046937798053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78313577739192697958532035 117470366608789046937798053)
        ·
          refine ⟨22025693739147946300837135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117470366608789046937798053 22025693739147946300837135)
          ·
            refine ⟨33038540608721919451255703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22025693739147946300837135 33038540608721919451255703)
            ·
              refine ⟨49557810913082879176883555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33038540608721919451255703 49557810913082879176883555)
              ·
                refine ⟨74336716369624318765325333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49557810913082879176883555 74336716369624318765325333)
                ·
                  refine ⟨3484533579826139942124625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74336716369624318765325333 3484533579826139942124625)
                  ·
                    refine ⟨2613400184869604956593469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3484533579826139942124625 2613400184869604956593469)
                    ·
                      refine ⟨980025069326101858722551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613400184869604956593469 980025069326101858722551)
                      ·
                        rfl

theorem cell23_1908592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_1908592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908592 prefixEnd_1908592 := by exact prefixLift 1908592
  have htrace : WordTrace (prefixWord ++ tailWord_1908592) baseStart_1908592 baseEnd_1908592 := by
    simpa [prefixWord, tailWord_1908592, baseEnd_1908592] using wordTrace_append hprefix tailTrace_1908592
  have hstable : (prefixWord ++ tailWord_1908592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908592).length < 2 ^ (prefixWord ++ tailWord_1908592).sum := by decide
  have hdescent : baseEnd_1908592 < baseStart_1908592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908606 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1908606 : Nat := 118140960795 + 1908606 * 2 ^ 59
def prefixEnd_1908606 : Nat := 4983230072969 + 3 ^ 40 * 1908606 * 2
def baseEnd_1908606 : Nat := 980032258055264803947487

theorem tailTrace_1908606 : CollatzResearch.WordTrace tailWord_1908606 prefixEnd_1908606 980032258055264803947487 := by
  unfold tailWord_1908606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701572465431737599824209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46408386482302600532395781 8701572465431737599824209)
  ·
    refine ⟨6526179349073803199868157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8701572465431737599824209 6526179349073803199868157)
    ·
      refine ⟨2447317255902676199950559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6526179349073803199868157 2447317255902676199950559)
      ·
        refine ⟨3670975883854014299925839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447317255902676199950559 3670975883854014299925839)
        ·
          refine ⟨5506463825781021449888759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3670975883854014299925839 5506463825781021449888759)
          ·
            refine ⟨8259695738671532174833139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506463825781021449888759 8259695738671532174833139)
            ·
              refine ⟨12389543608007298262249709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259695738671532174833139 12389543608007298262249709)
              ·
                refine ⟨4646078853002736848343641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12389543608007298262249709 4646078853002736848343641)
                ·
                  refine ⟨3484559139752052636257731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646078853002736848343641 3484559139752052636257731)
                  ·
                    refine ⟨5226838709628078954386597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3484559139752052636257731 5226838709628078954386597)
                    ·
                      refine ⟨980032258055264803947487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5226838709628078954386597 980032258055264803947487)
                      ·
                        rfl

theorem cell23_1908606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1908606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908606 prefixEnd_1908606 := by exact prefixLift 1908606
  have htrace : WordTrace (prefixWord ++ tailWord_1908606) baseStart_1908606 baseEnd_1908606 := by
    simpa [prefixWord, tailWord_1908606, baseEnd_1908606] using wordTrace_append hprefix tailTrace_1908606
  have hstable : (prefixWord ++ tailWord_1908606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908606).length < 2 ^ (prefixWord ++ tailWord_1908606).sum := by decide
  have hdescent : baseEnd_1908606 < baseStart_1908606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908626 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1908626 : Nat := 118140960795 + 1908626 * 2 ^ 59
def prefixEnd_1908626 : Nat := 4983230072969 + 3 ^ 40 * 1908626 * 2
def baseEnd_1908626 : Nat := 980042527668354725697395

theorem tailTrace_1908626 : CollatzResearch.WordTrace tailWord_1908626 prefixEnd_1908626 980042527668354725697395 := by
  unfold tailWord_1908626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17403327295845361053580433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46408872788920962809547821 17403327295845361053580433)
  ·
    refine ⟨13052495471884020790185325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17403327295845361053580433 13052495471884020790185325)
    ·
      refine ⟨4894685801956507796319497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13052495471884020790185325 4894685801956507796319497)
      ·
        refine ⟨3671014351467380847239623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4894685801956507796319497 3671014351467380847239623)
        ·
          refine ⟨5506521527201071270859435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3671014351467380847239623 5506521527201071270859435)
          ·
            refine ⟨8259782290801606906289153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506521527201071270859435 8259782290801606906289153)
            ·
              refine ⟨6194836718101205179716865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8259782290801606906289153 6194836718101205179716865)
              ·
                refine ⟨4646127538575903884787649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194836718101205179716865 4646127538575903884787649)
                ·
                  refine ⟨3484595653931927913590737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646127538575903884787649 3484595653931927913590737)
                  ·
                    refine ⟨2613446740448945935193053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3484595653931927913590737 2613446740448945935193053)
                    ·
                      refine ⟨980042527668354725697395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613446740448945935193053 980042527668354725697395)
                      ·
                        rfl

theorem cell23_1908626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1908626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908626 prefixEnd_1908626 := by exact prefixLift 1908626
  have htrace : WordTrace (prefixWord ++ tailWord_1908626) baseStart_1908626 baseEnd_1908626 := by
    simpa [prefixWord, tailWord_1908626, baseEnd_1908626] using wordTrace_append hprefix tailTrace_1908626
  have hstable : (prefixWord ++ tailWord_1908626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908626).length < 2 ^ (prefixWord ++ tailWord_1908626).sum := by decide
  have hdescent : baseEnd_1908626 < baseStart_1908626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908660 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1908660 : Nat := 118140960795 + 1908660 * 2 ^ 59
def prefixEnd_1908660 : Nat := 4983230072969 + 3 ^ 40 * 1908660 * 2
def baseEnd_1908660 : Nat := 980059986010607592672239

theorem tailTrace_1908660 : CollatzResearch.WordTrace tailWord_1908660 prefixEnd_1908660 980059986010607592672239 := by
  unfold tailWord_1908660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34807274632629134010529717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46409699510172178680706289 34807274632629134010529717)
  ·
    refine ⟨3263181996808981313487161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34807274632629134010529717 3263181996808981313487161)
    ·
      refine ⟨2447386497606735985115371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3263181996808981313487161 2447386497606735985115371)
      ·
        refine ⟨3671079746410103977673057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447386497606735985115371 3671079746410103977673057)
        ·
          refine ⟨2753309809807577983254793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3671079746410103977673057 2753309809807577983254793)
          ·
            refine ⟨2064982357355683487441095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753309809807577983254793 2064982357355683487441095)
            ·
              refine ⟨3097473536033525231161643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064982357355683487441095 3097473536033525231161643)
              ·
                refine ⟨4646210304050287846742465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097473536033525231161643 4646210304050287846742465)
                ·
                  refine ⟨3484657728037715885056849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646210304050287846742465 3484657728037715885056849)
                  ·
                    refine ⟨2613493296028286913792637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3484657728037715885056849 2613493296028286913792637)
                    ·
                      refine ⟨980059986010607592672239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613493296028286913792637 980059986010607592672239)
                      ·
                        rfl

theorem cell23_1908660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1908660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908660 prefixEnd_1908660 := by exact prefixLift 1908660
  have htrace : WordTrace (prefixWord ++ tailWord_1908660) baseStart_1908660 baseEnd_1908660 := by
    simpa [prefixWord, tailWord_1908660, baseEnd_1908660] using wordTrace_append hprefix tailTrace_1908660
  have hstable : (prefixWord ++ tailWord_1908660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908660).length < 2 ^ (prefixWord ++ tailWord_1908660).sum := by decide
  have hdescent : baseEnd_1908660 < baseStart_1908660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908672 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 1, 6]
def baseStart_1908672 : Nat := 118140960795 + 1908672 * 2 ^ 59
def prefixEnd_1908672 : Nat := 4983230072969 + 3 ^ 40 * 1908672 * 2
def baseEnd_1908672 : Nat := 326688715926153848574061

theorem tailTrace_1908672 : CollatzResearch.WordTrace tailWord_1908672 prefixEnd_1908672 326688715926153848574061 := by
  unfold tailWord_1908672
  simp only [CollatzResearch.WordTrace]
  refine ⟨34807493470607397035248135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46409991294143196046997513 34807493470607397035248135)
  ·
    refine ⟨52211240205911095552872203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34807493470607397035248135 52211240205911095552872203)
    ·
      refine ⟨78316860308866643329308305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52211240205911095552872203 78316860308866643329308305)
      ·
        refine ⟨58737645231649982496981229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78316860308866643329308305 58737645231649982496981229)
        ·
          refine ⟨22026616961868743436367961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58737645231649982496981229 22026616961868743436367961)
          ·
            refine ⟨16519962721401557577275971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22026616961868743436367961 16519962721401557577275971)
            ·
              refine ⟨24779944082102336365913957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16519962721401557577275971 24779944082102336365913957)
              ·
                refine ⟨4646239515394188068608867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24779944082102336365913957 4646239515394188068608867)
                ·
                  refine ⟨6969359273091282102913301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4646239515394188068608867 6969359273091282102913301)
                  ·
                    refine ⟨326688715926153848574061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6969359273091282102913301 326688715926153848574061)
                    ·
                      rfl

theorem cell23_1908672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_1908672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908672 prefixEnd_1908672 := by exact prefixLift 1908672
  have htrace : WordTrace (prefixWord ++ tailWord_1908672) baseStart_1908672 baseEnd_1908672 := by
    simpa [prefixWord, tailWord_1908672, baseEnd_1908672] using wordTrace_append hprefix tailTrace_1908672
  have hstable : (prefixWord ++ tailWord_1908672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908672).length < 2 ^ (prefixWord ++ tailWord_1908672).sum := by decide
  have hdescent : baseEnd_1908672 < baseStart_1908672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908689 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 2, 4]
def baseStart_1908689 : Nat := 118140960795 + 1908689 * 2 ^ 59
def prefixEnd_1908689 : Nat := 4983230072969 + 3 ^ 40 * 1908689 * 2
def baseEnd_1908689 : Nat := 326691625649862659736535

theorem tailTrace_1908689 : CollatzResearch.WordTrace tailWord_1908689 prefixEnd_1908689 326691625649862659736535 := by
  unfold tailWord_1908689
  simp only [CollatzResearch.WordTrace]
  refine ⟨69615606982153205973865121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46410404654768803982576747 69615606982153205973865121)
  ·
    refine ⟨52211705236614904480398841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69615606982153205973865121 52211705236614904480398841)
    ·
      refine ⟨39158778927461178360299131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52211705236614904480398841 39158778927461178360299131)
      ·
        refine ⟨58738168391191767540448697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39158778927461178360299131 58738168391191767540448697)
        ·
          refine ⟨44053626293393825655336523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58738168391191767540448697 44053626293393825655336523)
          ·
            refine ⟨66080439440090738483004785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44053626293393825655336523 66080439440090738483004785)
            ·
              refine ⟨49560329580068053862253589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66080439440090738483004785 49560329580068053862253589)
              ·
                refine ⟨2323140449065690024793137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49560329580068053862253589 2323140449065690024793137)
                ·
                  refine ⟨1742355336799267518594853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2323140449065690024793137 1742355336799267518594853)
                  ·
                    refine ⟨326691625649862659736535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1742355336799267518594853 326691625649862659736535)
                    ·
                      rfl

theorem cell23_1908689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_1908689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908689 prefixEnd_1908689 := by exact prefixLift 1908689
  have htrace : WordTrace (prefixWord ++ tailWord_1908689) baseStart_1908689 baseEnd_1908689 := by
    simpa [prefixWord, tailWord_1908689, baseEnd_1908689] using wordTrace_append hprefix tailTrace_1908689
  have hstable : (prefixWord ++ tailWord_1908689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908689).length < 2 ^ (prefixWord ++ tailWord_1908689).sum := by decide
  have hdescent : baseEnd_1908689 < baseStart_1908689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908752 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_1908752 : Nat := 118140960795 + 1908752 * 2 ^ 59
def prefixEnd_1908752 : Nat := 4983230072969 + 3 ^ 40 * 1908752 * 2
def baseEnd_1908752 : Nat := 980107226230821232721815

theorem tailTrace_1908752 : CollatzResearch.WordTrace tailWord_1908752 prefixEnd_1908752 980107226230821232721815 := by
  unfold tailWord_1908752
  simp only [CollatzResearch.WordTrace]
  refine ⟨34808952390462483866704255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46411936520616645155605673 34808952390462483866704255)
  ·
    refine ⟨52213428585693725800056383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34808952390462483866704255 52213428585693725800056383)
    ·
      refine ⟨78320142878540588700084575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52213428585693725800056383 78320142878540588700084575)
      ·
        refine ⟨117480214317810883050126863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78320142878540588700084575 117480214317810883050126863)
        ·
          refine ⟨176220321476716324575190295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117480214317810883050126863 176220321476716324575190295)
          ·
            refine ⟨264330482215074486862785443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176220321476716324575190295 264330482215074486862785443)
            ·
              refine ⟨396495723322611730294178165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264330482215074486862785443 396495723322611730294178165)
              ·
                refine ⟨37171474061494849715079203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396495723322611730294178165 37171474061494849715079203)
                ·
                  refine ⟨55757211092242274572618805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37171474061494849715079203 55757211092242274572618805)
                  ·
                    refine ⟨5227238539897713241183013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55757211092242274572618805 5227238539897713241183013)
                    ·
                      refine ⟨980107226230821232721815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5227238539897713241183013 980107226230821232721815)
                      ·
                        rfl

theorem cell23_1908752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_1908752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908752 prefixEnd_1908752 := by exact prefixLift 1908752
  have htrace : WordTrace (prefixWord ++ tailWord_1908752) baseStart_1908752 baseEnd_1908752 := by
    simpa [prefixWord, tailWord_1908752, baseEnd_1908752] using wordTrace_append hprefix tailTrace_1908752
  have hstable : (prefixWord ++ tailWord_1908752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908752).length < 2 ^ (prefixWord ++ tailWord_1908752).sum := by decide
  have hdescent : baseEnd_1908752 < baseStart_1908752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908773 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 1, 3, 2]
def baseStart_1908773 : Nat := 118140960795 + 1908773 * 2 ^ 59
def prefixEnd_1908773 : Nat := 4983230072969 + 3 ^ 40 * 1908773 * 2
def baseEnd_1908773 : Nat := 980118009324565650559219

theorem tailTrace_1908773 : CollatzResearch.WordTrace tailWord_1908773 prefixEnd_1908773 980118009324565650559219 := by
  unfold tailWord_1908773
  simp only [CollatzResearch.WordTrace]
  refine ⟨69618670713848888319922973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46412447142565925546615315 69618670713848888319922973)
  ·
    refine ⟨26107001517693333119971115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69618670713848888319922973 26107001517693333119971115)
    ·
      refine ⟨39160502276539999679956673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26107001517693333119971115 39160502276539999679956673)
      ·
        refine ⟨29370376707404999759967505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39160502276539999679956673 29370376707404999759967505)
        ·
          refine ⟨22027782530553749819975629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29370376707404999759967505 22027782530553749819975629)
          ·
            refine ⟨8260418448957656182490861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22027782530553749819975629 8260418448957656182490861)
            ·
              refine ⟨3097656918359121068434073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8260418448957656182490861 3097656918359121068434073)
              ·
                refine ⟨2323242688769340801325555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3097656918359121068434073 2323242688769340801325555)
                ·
                  refine ⟨3484864033154011201988333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323242688769340801325555 3484864033154011201988333)
                  ·
                    refine ⟨1306824012432754200745625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484864033154011201988333 1306824012432754200745625)
                    ·
                      refine ⟨980118009324565650559219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306824012432754200745625 980118009324565650559219)
                      ·
                        rfl

theorem cell23_1908773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_1908773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908773 prefixEnd_1908773 := by exact prefixLift 1908773
  have htrace : WordTrace (prefixWord ++ tailWord_1908773) baseStart_1908773 baseEnd_1908773 := by
    simpa [prefixWord, tailWord_1908773, baseEnd_1908773] using wordTrace_append hprefix tailTrace_1908773
  have hstable : (prefixWord ++ tailWord_1908773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908773).length < 2 ^ (prefixWord ++ tailWord_1908773).sum := by decide
  have hdescent : baseEnd_1908773 < baseStart_1908773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908786 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_1908786 : Nat := 118140960795 + 1908786 * 2 ^ 59
def prefixEnd_1908786 : Nat := 4983230072969 + 3 ^ 40 * 1908786 * 2
def baseEnd_1908786 : Nat := 980124684573074099696659

theorem tailTrace_1908786 : CollatzResearch.WordTrace tailWord_1908786 prefixEnd_1908786 980124684573074099696659 := by
  unfold tailWord_1908786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404786215700447885036553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46412763241867861026764141 17404786215700447885036553)
  ·
    refine ⟨13053589661775335913777415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17404786215700447885036553 13053589661775335913777415)
    ·
      refine ⟨19580384492663003870666123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13053589661775335913777415 19580384492663003870666123)
      ·
        refine ⟨29370576738994505805999185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19580384492663003870666123 29370576738994505805999185)
        ·
          refine ⟨22027932554245879354499389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29370576738994505805999185 22027932554245879354499389)
          ·
            refine ⟨8260474707842204757937271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22027932554245879354499389 8260474707842204757937271)
            ·
              refine ⟨12390712061763307136905907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260474707842204757937271 12390712061763307136905907)
              ·
                refine ⟨18586068092644960705358861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12390712061763307136905907 18586068092644960705358861)
                ·
                  refine ⟨6969775534741860264509573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18586068092644960705358861 6969775534741860264509573)
                  ·
                    refine ⟨1306832912764098799595545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969775534741860264509573 1306832912764098799595545)
                    ·
                      refine ⟨980124684573074099696659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306832912764098799595545 980124684573074099696659)
                      ·
                        rfl

theorem cell23_1908786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_1908786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908786 prefixEnd_1908786 := by exact prefixLift 1908786
  have htrace : WordTrace (prefixWord ++ tailWord_1908786) baseStart_1908786 baseEnd_1908786 := by
    simpa [prefixWord, tailWord_1908786, baseEnd_1908786] using wordTrace_append hprefix tailTrace_1908786
  have hstable : (prefixWord ++ tailWord_1908786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908786).length < 2 ^ (prefixWord ++ tailWord_1908786).sum := by decide
  have hdescent : baseEnd_1908786 < baseStart_1908786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908789 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1908789 : Nat := 118140960795 + 1908789 * 2 ^ 59
def prefixEnd_1908789 : Nat := 4983230072969 + 3 ^ 40 * 1908789 * 2
def baseEnd_1908789 : Nat := 980126225015037587959145

theorem tailTrace_1908789 : CollatzResearch.WordTrace tailWord_1908789 prefixEnd_1908789 980126225015037587959145 := by
  unfold tailWord_1908789
  simp only [CollatzResearch.WordTrace]
  refine ⟨69619254281790923052505421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46412836187860615368336947 69619254281790923052505421)
  ·
    refine ⟨26107220355671596144689533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69619254281790923052505421 26107220355671596144689533)
    ·
      refine ⟨9790207633376848554258575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26107220355671596144689533 9790207633376848554258575)
      ·
        refine ⟨14685311450065272831387863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9790207633376848554258575 14685311450065272831387863)
        ·
          refine ⟨22027967175097909247081795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14685311450065272831387863 22027967175097909247081795)
          ·
            refine ⟨33041950762646863870622693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22027967175097909247081795 33041950762646863870622693)
            ·
              refine ⟨6195365767996286975741755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33041950762646863870622693 6195365767996286975741755)
              ·
                refine ⟨9293048651994430463612633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195365767996286975741755 9293048651994430463612633)
                ·
                  refine ⟨6969786488995822847709475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9293048651994430463612633 6969786488995822847709475)
                  ·
                    refine ⟨10454679733493734271564213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6969786488995822847709475 10454679733493734271564213)
                    ·
                      refine ⟨980126225015037587959145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10454679733493734271564213 980126225015037587959145)
                      ·
                        rfl

theorem cell23_1908789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1908789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908789 prefixEnd_1908789 := by exact prefixLift 1908789
  have htrace : WordTrace (prefixWord ++ tailWord_1908789) baseStart_1908789 baseEnd_1908789 := by
    simpa [prefixWord, tailWord_1908789, baseEnd_1908789] using wordTrace_append hprefix tailTrace_1908789
  have hstable : (prefixWord ++ tailWord_1908789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908789).length < 2 ^ (prefixWord ++ tailWord_1908789).sum := by decide
  have hdescent : baseEnd_1908789 < baseStart_1908789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908839 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1908839 : Nat := 118140960795 + 1908839 * 2 ^ 59
def prefixEnd_1908839 : Nat := 4983230072969 + 3 ^ 40 * 1908839 * 2
def baseEnd_1908839 : Nat := 326717299682587464111305

theorem tailTrace_1908839 : CollatzResearch.WordTrace tailWord_1908839 prefixEnd_1908839 326717299682587464111305 := by
  unfold tailWord_1908839
  simp only [CollatzResearch.WordTrace]
  refine ⟨69621077931609781591825571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46414051954406521061217047 69621077931609781591825571)
  ·
    refine ⟨104431616897414672387738357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69621077931609781591825571 104431616897414672387738357)
    ·
      refine ⟨9790464084132625536350471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104431616897414672387738357 9790464084132625536350471)
      ·
        refine ⟨14685696126198938304525707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9790464084132625536350471 14685696126198938304525707)
        ·
          refine ⟨22028544189298407456788561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14685696126198938304525707 22028544189298407456788561)
          ·
            refine ⟨16521408141973805592591421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22028544189298407456788561 16521408141973805592591421)
            ·
              refine ⟨6195528053240177097221783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16521408141973805592591421 6195528053240177097221783)
              ·
                refine ⟨9293292079860265645832675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195528053240177097221783 9293292079860265645832675)
                ·
                  refine ⟨13939938119790398468749013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9293292079860265645832675 13939938119790398468749013)
                  ·
                    refine ⟨326717299682587464111305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13939938119790398468749013 326717299682587464111305)
                    ·
                      rfl

theorem cell23_1908839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1908839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908839 prefixEnd_1908839 := by exact prefixLift 1908839
  have htrace : WordTrace (prefixWord ++ tailWord_1908839) baseStart_1908839 baseEnd_1908839 := by
    simpa [prefixWord, tailWord_1908839, baseEnd_1908839] using wordTrace_append hprefix tailTrace_1908839
  have hstable : (prefixWord ++ tailWord_1908839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908839).length < 2 ^ (prefixWord ++ tailWord_1908839).sum := by decide
  have hdescent : baseEnd_1908839 < baseStart_1908839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908896 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1908896 : Nat := 118140960795 + 1908896 * 2 ^ 59
def prefixEnd_1908896 : Nat := 4983230072969 + 3 ^ 40 * 1908896 * 2
def baseEnd_1908896 : Nat := 980181167445068669321153

theorem tailTrace_1908896 : CollatzResearch.WordTrace tailWord_1908896 prefixEnd_1908896 980181167445068669321153 := by
  unfold tailWord_1908896
  simp only [CollatzResearch.WordTrace]
  refine ⟨34811578446201640163325271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46415437928268853551100361 34811578446201640163325271)
  ·
    refine ⟨52217367669302460244987907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34811578446201640163325271 52217367669302460244987907)
    ·
      refine ⟨78326051503953690367481861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52217367669302460244987907 78326051503953690367481861)
      ·
        refine ⟨14686134656991316943902849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78326051503953690367481861 14686134656991316943902849)
        ·
          refine ⟨11014600992743487707927137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14686134656991316943902849 11014600992743487707927137)
          ·
            refine ⟨8260950744557615780945353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11014600992743487707927137 8260950744557615780945353)
            ·
              refine ⟨6195713058418211835709015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8260950744557615780945353 6195713058418211835709015)
              ·
                refine ⟨9293569587627317753563523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195713058418211835709015 9293569587627317753563523)
                ·
                  refine ⟨13940354381440976630345285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9293569587627317753563523 13940354381440976630345285)
                  ·
                    refine ⟨2613816446520183118189741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13940354381440976630345285 2613816446520183118189741)
                    ·
                      refine ⟨980181167445068669321153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613816446520183118189741 980181167445068669321153)
                      ·
                        rfl

theorem cell23_1908896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1908896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908896 prefixEnd_1908896 := by exact prefixLift 1908896
  have htrace : WordTrace (prefixWord ++ tailWord_1908896) baseStart_1908896 baseEnd_1908896 := by
    simpa [prefixWord, tailWord_1908896, baseEnd_1908896] using wordTrace_append hprefix tailTrace_1908896
  have hstable : (prefixWord ++ tailWord_1908896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908896).length < 2 ^ (prefixWord ++ tailWord_1908896).sum := by decide
  have hdescent : baseEnd_1908896 < baseStart_1908896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908920 : List Nat := [2, 1, 2, 1, 2, 1, 7, 2, 1, 4]
def baseStart_1908920 : Nat := 118140960795 + 1908920 * 2 ^ 59
def prefixEnd_1908920 : Nat := 4983230072969 + 3 ^ 40 * 1908920 * 2
def baseEnd_1908920 : Nat := 326731163660258858473681

theorem tailTrace_1908920 : CollatzResearch.WordTrace tailWord_1908920 prefixEnd_1908920 326731163660258858473681 := by
  unfold tailWord_1908920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34812016122158166212762107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46416021496210888283682809 34812016122158166212762107)
  ·
    refine ⟨52218024183237249319143161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34812016122158166212762107 52218024183237249319143161)
    ·
      refine ⟨39163518137427936989357371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52218024183237249319143161 39163518137427936989357371)
      ·
        refine ⟨58745277206141905484036057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39163518137427936989357371 58745277206141905484036057)
        ·
          refine ⟨44058957904606429113027043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58745277206141905484036057 44058957904606429113027043)
          ·
            refine ⟨66088436856909643669540565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44058957904606429113027043 66088436856909643669540565)
            ·
              refine ⟨1548947738833819773504857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66088436856909643669540565 1548947738833819773504857)
              ·
                refine ⟨1161710804125364830128643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548947738833819773504857 1161710804125364830128643)
                ·
                  refine ⟨1742566206188047245192965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161710804125364830128643 1742566206188047245192965)
                  ·
                    refine ⟨326731163660258858473681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1742566206188047245192965 326731163660258858473681)
                    ·
                      rfl

theorem cell23_1908920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_1908920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908920 prefixEnd_1908920 := by exact prefixLift 1908920
  have htrace : WordTrace (prefixWord ++ tailWord_1908920) baseStart_1908920 baseEnd_1908920 := by
    simpa [prefixWord, tailWord_1908920, baseEnd_1908920] using wordTrace_append hprefix tailTrace_1908920
  have hstable : (prefixWord ++ tailWord_1908920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908920).length < 2 ^ (prefixWord ++ tailWord_1908920).sum := by decide
  have hdescent : baseEnd_1908920 < baseStart_1908920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908953 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 2, 3, 2]
def baseStart_1908953 : Nat := 118140960795 + 1908953 * 2 ^ 59
def prefixEnd_1908953 : Nat := 4983230072969 + 3 ^ 40 * 1908953 * 2
def baseEnd_1908953 : Nat := 980210435842374946308391

theorem tailTrace_1908953 : CollatzResearch.WordTrace tailWord_1908953 prefixEnd_1908953 980210435842374946308391 := by
  unfold tailWord_1908953
  simp only [CollatzResearch.WordTrace]
  refine ⟨69625235853196779061475513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46416823902131186040983675 69625235853196779061475513)
  ·
    refine ⟨52218926889897584296106635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69625235853196779061475513 52218926889897584296106635)
    ·
      refine ⟨78328390334846376444159953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52218926889897584296106635 78328390334846376444159953)
      ·
        refine ⟨58746292751134782333119965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78328390334846376444159953 58746292751134782333119965)
        ·
          refine ⟨22029859781675543374919987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58746292751134782333119965 22029859781675543374919987)
          ·
            refine ⟨33044789672513315062379981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22029859781675543374919987 33044789672513315062379981)
            ·
              refine ⟨12391796127192493148392493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33044789672513315062379981 12391796127192493148392493)
              ·
                refine ⟨4646923547697184930647185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12391796127192493148392493 4646923547697184930647185)
                ·
                  refine ⟨3485192660772888697985389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646923547697184930647185 3485192660772888697985389)
                  ·
                    refine ⟨1306947247789833261744521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485192660772888697985389 1306947247789833261744521)
                    ·
                      refine ⟨980210435842374946308391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306947247789833261744521 980210435842374946308391)
                      ·
                        rfl

theorem cell23_1908953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_1908953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908953 prefixEnd_1908953 := by exact prefixLift 1908953
  have htrace : WordTrace (prefixWord ++ tailWord_1908953) baseStart_1908953 baseEnd_1908953 := by
    simpa [prefixWord, tailWord_1908953, baseEnd_1908953] using wordTrace_append hprefix tailTrace_1908953
  have hstable : (prefixWord ++ tailWord_1908953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908953).length < 2 ^ (prefixWord ++ tailWord_1908953).sum := by decide
  have hdescent : baseEnd_1908953 < baseStart_1908953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908960 : List Nat := [2, 1, 1, 3, 1, 3, 2, 5, 1, 1, 3]
def baseStart_1908960 : Nat := 118140960795 + 1908960 * 2 ^ 59
def prefixEnd_1908960 : Nat := 4983230072969 + 3 ^ 40 * 1908960 * 2
def baseEnd_1908960 : Nat := 980214030206956418920859

theorem tailTrace_1908960 : CollatzResearch.WordTrace tailWord_1908960 prefixEnd_1908960 980214030206956418920859 := by
  unfold tailWord_1908960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34812745582085709628490167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46416994109447612837986889 34812745582085709628490167)
  ·
    refine ⟨52219118373128564442735251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34812745582085709628490167 52219118373128564442735251)
    ·
      refine ⟨78328677559692846664102877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52219118373128564442735251 78328677559692846664102877)
      ·
        refine ⟨29373254084884817499038579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78328677559692846664102877 29373254084884817499038579)
        ·
          refine ⟨44059881127327226248557869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29373254084884817499038579 44059881127327226248557869)
          ·
            refine ⟨16522455422747709843209201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44059881127327226248557869 16522455422747709843209201)
            ·
              refine ⟨12391841567060782382406901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16522455422747709843209201 12391841567060782382406901)
              ·
                refine ⟨1161735146911948348350647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12391841567060782382406901 1161735146911948348350647)
                ·
                  refine ⟨1742602720367922522525971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161735146911948348350647 1742602720367922522525971)
                  ·
                    refine ⟨2613904080551883783788957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1742602720367922522525971 2613904080551883783788957)
                    ·
                      refine ⟨980214030206956418920859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613904080551883783788957 980214030206956418920859)
                      ·
                        rfl

theorem cell23_1908960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_1908960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908960 prefixEnd_1908960 := by exact prefixLift 1908960
  have htrace : WordTrace (prefixWord ++ tailWord_1908960) baseStart_1908960 baseEnd_1908960 := by
    simpa [prefixWord, tailWord_1908960, baseEnd_1908960] using wordTrace_append hprefix tailTrace_1908960
  have hstable : (prefixWord ++ tailWord_1908960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908960).length < 2 ^ (prefixWord ++ tailWord_1908960).sum := by decide
  have hdescent : baseEnd_1908960 < baseStart_1908960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908976 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 4, 4]
def baseStart_1908976 : Nat := 118140960795 + 1908976 * 2 ^ 59
def prefixEnd_1908976 : Nat := 4983230072969 + 3 ^ 40 * 1908976 * 2
def baseEnd_1908976 : Nat := 326740748632476118773595

theorem tailTrace_1908976 : CollatzResearch.WordTrace tailWord_1908976 prefixEnd_1908976 326740748632476118773595 := by
  unfold tailWord_1908976
  simp only [CollatzResearch.WordTrace]
  refine ⟨34813037366056726994781391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46417383154742302659708521 34813037366056726994781391)
  ·
    refine ⟨52219556049085090492172087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34813037366056726994781391 52219556049085090492172087)
    ·
      refine ⟨78329334073627635738258131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52219556049085090492172087 78329334073627635738258131)
      ·
        refine ⟨117494001110441453607387197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78329334073627635738258131 117494001110441453607387197)
        ·
          refine ⟨44060250416415545102770199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117494001110441453607387197 44060250416415545102770199)
          ·
            refine ⟨66090375624623317654155299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44060250416415545102770199 66090375624623317654155299)
            ·
              refine ⟨99135563436934976481232949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66090375624623317654155299 99135563436934976481232949)
              ·
                refine ⟨9293959072212654045115589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99135563436934976481232949 9293959072212654045115589)
                ·
                  refine ⟨1742617326039872633459173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9293959072212654045115589 1742617326039872633459173)
                  ·
                    refine ⟨326740748632476118773595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1742617326039872633459173 326740748632476118773595)
                    ·
                      rfl

theorem cell23_1908976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_1908976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908976 prefixEnd_1908976 := by exact prefixLift 1908976
  have htrace : WordTrace (prefixWord ++ tailWord_1908976) baseStart_1908976 baseEnd_1908976 := by
    simpa [prefixWord, tailWord_1908976, baseEnd_1908976] using wordTrace_append hprefix tailTrace_1908976
  have hstable : (prefixWord ++ tailWord_1908976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908976).length < 2 ^ (prefixWord ++ tailWord_1908976).sum := by decide
  have hdescent : baseEnd_1908976 < baseStart_1908976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908977 : List Nat := [1, 2, 2, 2, 2, 1, 6, 2, 1, 1, 3]
def baseStart_1908977 : Nat := 118140960795 + 1908977 * 2 ^ 59
def prefixEnd_1908977 : Nat := 4983230072969 + 3 ^ 40 * 1908977 * 2
def baseEnd_1908977 : Nat := 980222759378082852408281

theorem tailTrace_1908977 : CollatzResearch.WordTrace tailWord_1908977 prefixEnd_1908977 980222759378082852408281 := by
  unfold tailWord_1908977
  simp only [CollatzResearch.WordTrace]
  refine ⟨69626111205109831160349185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46417407470073220773566123 69626111205109831160349185)
  ·
    refine ⟨52219583403832373370261889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69626111205109831160349185 52219583403832373370261889)
    ·
      refine ⟨39164687552874280027696417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52219583403832373370261889 39164687552874280027696417)
      ·
        refine ⟨29373515664655710020772313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39164687552874280027696417 29373515664655710020772313)
        ·
          refine ⟨22030136748491782515579235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29373515664655710020772313 22030136748491782515579235)
          ·
            refine ⟨33045205122737673773368853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22030136748491782515579235 33045205122737673773368853)
            ·
              refine ⟨1548993990128328458126665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33045205122737673773368853 1548993990128328458126665)
              ·
                refine ⟨1161745492596246343594999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548993990128328458126665 1161745492596246343594999)
                ·
                  refine ⟨1742618238894369515392499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161745492596246343594999 1742618238894369515392499)
                  ·
                    refine ⟨2613927358341554273088749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1742618238894369515392499 2613927358341554273088749)
                    ·
                      refine ⟨980222759378082852408281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613927358341554273088749 980222759378082852408281)
                      ·
                        rfl

theorem cell23_1908977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_1908977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908977 prefixEnd_1908977 := by exact prefixLift 1908977
  have htrace : WordTrace (prefixWord ++ tailWord_1908977) baseStart_1908977 baseEnd_1908977 := by
    simpa [prefixWord, tailWord_1908977, baseEnd_1908977] using wordTrace_append hprefix tailTrace_1908977
  have hstable : (prefixWord ++ tailWord_1908977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908977).length < 2 ^ (prefixWord ++ tailWord_1908977).sum := by decide
  have hdescent : baseEnd_1908977 < baseStart_1908977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908993 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1908993 : Nat := 118140960795 + 1908993 * 2 ^ 59
def prefixEnd_1908993 : Nat := 4983230072969 + 3 ^ 40 * 1908993 * 2
def baseEnd_1908993 : Nat := 326743658356184929936069

theorem tailTrace_1908993 : CollatzResearch.WordTrace tailWord_1908993 prefixEnd_1908993 326743658356184929936069 := by
  unfold tailWord_1908993
  simp only [CollatzResearch.WordTrace]
  refine ⟨69626694773051865892931633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46417796515367910595287755 69626694773051865892931633)
  ·
    refine ⟨52220021079788899419698725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69626694773051865892931633 52220021079788899419698725)
    ·
      refine ⟨9791253952460418641193511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52220021079788899419698725 9791253952460418641193511)
      ·
        refine ⟨14686880928690627961790267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9791253952460418641193511 14686880928690627961790267)
        ·
          refine ⟨22030321393035941942685401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14686880928690627961790267 22030321393035941942685401)
          ·
            refine ⟨16522741044776956457014051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22030321393035941942685401 16522741044776956457014051)
            ·
              refine ⟨24784111567165434685521077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16522741044776956457014051 24784111567165434685521077)
              ·
                refine ⟨2323510459421759501767601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24784111567165434685521077 2323510459421759501767601)
                ·
                  refine ⟨1742632844566319626325701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2323510459421759501767601 1742632844566319626325701)
                  ·
                    refine ⟨326743658356184929936069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1742632844566319626325701 326743658356184929936069)
                    ·
                      rfl

theorem cell23_1908993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1908993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1908993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1908993 prefixEnd_1908993 := by exact prefixLift 1908993
  have htrace : WordTrace (prefixWord ++ tailWord_1908993) baseStart_1908993 baseEnd_1908993 := by
    simpa [prefixWord, tailWord_1908993, baseEnd_1908993] using wordTrace_append hprefix tailTrace_1908993
  have hstable : (prefixWord ++ tailWord_1908993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908993).length < 2 ^ (prefixWord ++ tailWord_1908993).sum := by decide
  have hdescent : baseEnd_1908993 < baseStart_1908993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909000 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_1909000 : Nat := 118140960795 + 1909000 * 2 ^ 59
def prefixEnd_1909000 : Nat := 4983230072969 + 3 ^ 40 * 1909000 * 2
def baseEnd_1909000 : Nat := 980234569433136262420675

theorem tailTrace_1909000 : CollatzResearch.WordTrace tailWord_1909000 prefixEnd_1909000 980234569433136262420675 := by
  unfold tailWord_1909000
  simp only [CollatzResearch.WordTrace]
  refine ⟨34813475042013253044218227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46417966722684337392290969 34813475042013253044218227)
  ·
    refine ⟨52220212563019879566327341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34813475042013253044218227 52220212563019879566327341)
    ·
      refine ⟨19582579711132454837372753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52220212563019879566327341 19582579711132454837372753)
      ·
        refine ⟨14686934783349341128029565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19582579711132454837372753 14686934783349341128029565)
        ·
          refine ⟨5507600543756002923011087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14686934783349341128029565 5507600543756002923011087)
          ·
            refine ⟨8261400815634004384516631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5507600543756002923011087 8261400815634004384516631)
            ·
              refine ⟨12392101223451006576774947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8261400815634004384516631 12392101223451006576774947)
              ·
                refine ⟨18588151835176509865162421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12392101223451006576774947 18588151835176509865162421)
                ·
                  refine ⟨1742639234547797799858977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18588151835176509865162421 1742639234547797799858977)
                  ·
                    refine ⟨1306979425910848349894233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1742639234547797799858977 1306979425910848349894233)
                    ·
                      refine ⟨980234569433136262420675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1306979425910848349894233 980234569433136262420675)
                      ·
                        rfl

theorem cell23_1909000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_1909000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909000 prefixEnd_1909000 := by exact prefixLift 1909000
  have htrace : WordTrace (prefixWord ++ tailWord_1909000) baseStart_1909000 baseEnd_1909000 := by
    simpa [prefixWord, tailWord_1909000, baseEnd_1909000] using wordTrace_append hprefix tailTrace_1909000
  have hstable : (prefixWord ++ tailWord_1909000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909000).length < 2 ^ (prefixWord ++ tailWord_1909000).sum := by decide
  have hdescent : baseEnd_1909000 < baseStart_1909000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909003 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 3]
def baseStart_1909003 : Nat := 118140960795 + 1909003 * 2 ^ 59
def prefixEnd_1909003 : Nat := 4983230072969 + 3 ^ 40 * 1909003 * 2
def baseEnd_1909003 : Nat := 980236109875099750683161

theorem tailTrace_1909003 : CollatzResearch.WordTrace tailWord_1909003 prefixEnd_1909003 980236109875099750683161 := by
  unfold tailWord_1909003
  simp only [CollatzResearch.WordTrace]
  refine ⟨69627059503015637600795663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46418039668677091733863775 69627059503015637600795663)
  ·
    refine ⟨104440589254523456401193495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69627059503015637600795663 104440589254523456401193495)
    ·
      refine ⟨156660883881785184601790243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104440589254523456401193495 156660883881785184601790243)
      ·
        refine ⟨234991325822677776902685365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156660883881785184601790243 234991325822677776902685365)
        ·
          refine ⟨22030436795876041584626753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234991325822677776902685365 22030436795876041584626753)
          ·
            refine ⟨16522827596907031188470065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22030436795876041584626753 16522827596907031188470065)
            ·
              refine ⟨12392120697680273391352549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16522827596907031188470065 12392120697680273391352549)
              ·
                refine ⟨2323522630815051260878603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12392120697680273391352549 2323522630815051260878603)
                ·
                  refine ⟨3485283946222576891317905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323522630815051260878603 3485283946222576891317905)
                  ·
                    refine ⟨2613962959666932668488429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3485283946222576891317905 2613962959666932668488429)
                    ·
                      refine ⟨980236109875099750683161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2613962959666932668488429 980236109875099750683161)
                      ·
                        rfl

theorem cell23_1909003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 3].length) (baseStart_1909003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909003 prefixEnd_1909003 := by exact prefixLift 1909003
  have htrace : WordTrace (prefixWord ++ tailWord_1909003) baseStart_1909003 baseEnd_1909003 := by
    simpa [prefixWord, tailWord_1909003, baseEnd_1909003] using wordTrace_append hprefix tailTrace_1909003
  have hstable : (prefixWord ++ tailWord_1909003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909003).length < 2 ^ (prefixWord ++ tailWord_1909003).sum := by decide
  have hdescent : baseEnd_1909003 < baseStart_1909003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909034 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1909034 : Nat := 118140960795 + 1909034 * 2 ^ 59
def prefixEnd_1909034 : Nat := 4983230072969 + 3 ^ 40 * 1909034 * 2
def baseEnd_1909034 : Nat := 980252027775389129395519

theorem tailTrace_1909034 : CollatzResearch.WordTrace tailWord_1909034 prefixEnd_1909034 980252027775389129395519 := by
  unfold tailWord_1909034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17407047541475832473793539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46418793443935553263449437 17407047541475832473793539)
  ·
    refine ⟨26110571312213748710690309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17407047541475832473793539 26110571312213748710690309)
    ·
      refine ⟨4895732121040077883254433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26110571312213748710690309 4895732121040077883254433)
      ·
        refine ⟨3671799090780058412440825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4895732121040077883254433 3671799090780058412440825)
        ·
          refine ⟨2753849318085043809330619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3671799090780058412440825 2753849318085043809330619)
          ·
            refine ⟨4130773977127565713995929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753849318085043809330619 4130773977127565713995929)
            ·
              refine ⟨3098080482845674285496947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130773977127565713995929 3098080482845674285496947)
              ·
                refine ⟨4647120724268511428245421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098080482845674285496947 4647120724268511428245421)
                ·
                  refine ⟨1742670271600691785592033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4647120724268511428245421 1742670271600691785592033)
                  ·
                    refine ⟨1307002703700518839194025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1742670271600691785592033 1307002703700518839194025)
                    ·
                      refine ⟨980252027775389129395519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307002703700518839194025 980252027775389129395519)
                      ·
                        rfl

theorem cell23_1909034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1909034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909034 prefixEnd_1909034 := by exact prefixLift 1909034
  have htrace : WordTrace (prefixWord ++ tailWord_1909034) baseStart_1909034 baseEnd_1909034 := by
    simpa [prefixWord, tailWord_1909034, baseEnd_1909034] using wordTrace_append hprefix tailTrace_1909034
  have hstable : (prefixWord ++ tailWord_1909034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909034).length < 2 ^ (prefixWord ++ tailWord_1909034).sum := by decide
  have hdescent : baseEnd_1909034 < baseStart_1909034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909050 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_1909050 : Nat := 118140960795 + 1909050 * 2 ^ 59
def prefixEnd_1909050 : Nat := 4983230072969 + 3 ^ 40 * 1909050 * 2
def baseEnd_1909050 : Nat := 980260243465861066795445

theorem tailTrace_1909050 : CollatzResearch.WordTrace tailWord_1909050 prefixEnd_1909050 980260243465861066795445 := by
  unfold tailWord_1909050
  simp only [CollatzResearch.WordTrace]
  refine ⟨17407193433461341156939151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46419182489230243085171069 17407193433461341156939151)
  ·
    refine ⟨26110790150192011735408727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17407193433461341156939151 26110790150192011735408727)
    ·
      refine ⟨39166185225288017603113091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26110790150192011735408727 39166185225288017603113091)
      ·
        refine ⟨58749277837932026404669637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39166185225288017603113091 58749277837932026404669637)
        ·
          refine ⟨11015489594612254950875557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58749277837932026404669637 11015489594612254950875557)
          ·
            refine ⟨2065404298989797803289167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11015489594612254950875557 2065404298989797803289167)
            ·
              refine ⟨3098106448484696704933751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065404298989797803289167 3098106448484696704933751)
              ·
                refine ⟨4647159672727045057400627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098106448484696704933751 4647159672727045057400627)
                ·
                  refine ⟨6970739509090567586100941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647159672727045057400627 6970739509090567586100941)
                  ·
                    refine ⟨2614027315908962844787853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6970739509090567586100941 2614027315908962844787853)
                    ·
                      refine ⟨980260243465861066795445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2614027315908962844787853 980260243465861066795445)
                      ·
                        rfl

theorem cell23_1909050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_1909050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909050 prefixEnd_1909050 := by exact prefixLift 1909050
  have htrace : WordTrace (prefixWord ++ tailWord_1909050) baseStart_1909050 baseEnd_1909050 := by
    simpa [prefixWord, tailWord_1909050, baseEnd_1909050] using wordTrace_append hprefix tailTrace_1909050
  have hstable : (prefixWord ++ tailWord_1909050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909050).length < 2 ^ (prefixWord ++ tailWord_1909050).sum := by decide
  have hdescent : baseEnd_1909050 < baseStart_1909050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909057 : List Nat := [1, 2, 5, 2, 3, 1, 2, 7]
def baseStart_1909057 : Nat := 118140960795 + 1909057 * 2 ^ 59
def prefixEnd_1909057 : Nat := 4983230072969 + 3 ^ 40 * 1909057 * 2
def baseEnd_1909057 : Nat := 36306068067794168126219

theorem tailTrace_1909057 : CollatzResearch.WordTrace tailWord_1909057 prefixEnd_1909057 36306068067794168126219 := by
  unfold tailWord_1909057
  simp only [CollatzResearch.WordTrace]
  refine ⟨69629029044820004823261425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46419352696546669882174283 69629029044820004823261425)
  ·
    refine ⟨52221771783615003617446069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69629029044820004823261425 52221771783615003617446069)
    ·
      refine ⟨4895791104713906589135569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52221771783615003617446069 4895791104713906589135569)
      ·
        refine ⟨3671843328535429941851677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4895791104713906589135569 3671843328535429941851677)
        ·
          refine ⟨1376941248200786228194379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3671843328535429941851677 1376941248200786228194379)
          ·
            refine ⟨2065411872301179342291569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376941248200786228194379 2065411872301179342291569)
            ·
              refine ⟨1549058904225884506718677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065411872301179342291569 1549058904225884506718677)
              ·
                refine ⟨36306068067794168126219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1549058904225884506718677 36306068067794168126219)
                ·
                  rfl

theorem cell23_1909057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 7].length) (baseStart_1909057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909057 prefixEnd_1909057 := by exact prefixLift 1909057
  have htrace : WordTrace (prefixWord ++ tailWord_1909057) baseStart_1909057 baseEnd_1909057 := by
    simpa [prefixWord, tailWord_1909057, baseEnd_1909057] using wordTrace_append hprefix tailTrace_1909057
  have hstable : (prefixWord ++ tailWord_1909057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909057).length < 2 ^ (prefixWord ++ tailWord_1909057).sum := by decide
  have hdescent : baseEnd_1909057 < baseStart_1909057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909143 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 2, 5]
def baseStart_1909143 : Nat := 118140960795 + 1909143 * 2 ^ 59
def prefixEnd_1909143 : Nat := 4983230072969 + 3 ^ 40 * 1909143 * 2
def baseEnd_1909143 : Nat := 326769332388909734310839

theorem tailTrace_1909143 : CollatzResearch.WordTrace tailWord_1909143 prefixEnd_1909143 326769332388909734310839 := by
  unfold tailWord_1909143
  simp only [CollatzResearch.WordTrace]
  refine ⟨69632165722508441510892083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46421443815005627673928055 69632165722508441510892083)
  ·
    refine ⟨104448248583762662266338125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69632165722508441510892083 104448248583762662266338125)
    ·
      refine ⟨39168093218910998349876797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104448248583762662266338125 39168093218910998349876797)
      ·
        refine ⟨14688034957091624381203799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39168093218910998349876797 14688034957091624381203799)
        ·
          refine ⟨22032052435637436571805699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14688034957091624381203799 22032052435637436571805699)
          ·
            refine ⟨33048078653456154857708549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22032052435637436571805699 33048078653456154857708549)
            ·
              refine ⟨6196514747523029035820353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33048078653456154857708549 6196514747523029035820353)
              ·
                refine ⟨4647386060642271776865265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6196514747523029035820353 4647386060642271776865265)
                ·
                  refine ⟨3485539545481703832648949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647386060642271776865265 3485539545481703832648949)
                  ·
                    refine ⟨326769332388909734310839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3485539545481703832648949 326769332388909734310839)
                    ·
                      rfl

theorem cell23_1909143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_1909143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909143 prefixEnd_1909143 := by exact prefixLift 1909143
  have htrace : WordTrace (prefixWord ++ tailWord_1909143) baseStart_1909143 baseEnd_1909143 := by
    simpa [prefixWord, tailWord_1909143, baseEnd_1909143] using wordTrace_append hprefix tailTrace_1909143
  have hstable : (prefixWord ++ tailWord_1909143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909143).length < 2 ^ (prefixWord ++ tailWord_1909143).sum := by decide
  have hdescent : baseEnd_1909143 < baseStart_1909143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909180 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1909180 : Nat := 118140960795 + 1909180 * 2 ^ 59
def prefixEnd_1909180 : Nat := 4983230072969 + 3 ^ 40 * 1909180 * 2
def baseEnd_1909180 : Nat := 980326995950945558169847

theorem tailTrace_1909180 : CollatzResearch.WordTrace tailWord_1909180 prefixEnd_1909180 980326995950945558169847 := by
  unfold tailWord_1909180
  simp only [CollatzResearch.WordTrace]
  refine ⟨34816757611687198414994497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46422343482249597886659329 34816757611687198414994497)
  ·
    refine ⟨26112568208765398811245873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34816757611687198414994497 26112568208765398811245873)
    ·
      refine ⟨19584426156574049108434405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26112568208765398811245873 19584426156574049108434405)
      ·
        refine ⟨3672079904357634207831451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19584426156574049108434405 3672079904357634207831451)
        ·
          refine ⟨5508119856536451311747177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672079904357634207831451 5508119856536451311747177)
          ·
            refine ⟨4131089892402338483810383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508119856536451311747177 4131089892402338483810383)
            ·
              refine ⟨6196634838603507725715575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131089892402338483810383 6196634838603507725715575)
              ·
                refine ⟨9294952257905261588573363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196634838603507725715575 9294952257905261588573363)
                ·
                  refine ⟨13942428386857892382860045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9294952257905261588573363 13942428386857892382860045)
                  ·
                    refine ⟨5228410645071709643572517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13942428386857892382860045 5228410645071709643572517)
                    ·
                      refine ⟨980326995950945558169847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5228410645071709643572517 980326995950945558169847)
                      ·
                        rfl

theorem cell23_1909180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1909180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909180 prefixEnd_1909180 := by exact prefixLift 1909180
  have htrace : WordTrace (prefixWord ++ tailWord_1909180) baseStart_1909180 baseEnd_1909180 := by
    simpa [prefixWord, tailWord_1909180, baseEnd_1909180] using wordTrace_append hprefix tailTrace_1909180
  have hstable : (prefixWord ++ tailWord_1909180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909180).length < 2 ^ (prefixWord ++ tailWord_1909180).sum := by decide
  have hdescent : baseEnd_1909180 < baseStart_1909180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909223 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1909223 : Nat := 118140960795 + 1909223 * 2 ^ 59
def prefixEnd_1909223 : Nat := 4983230072969 + 3 ^ 40 * 1909223 * 2
def baseEnd_1909223 : Nat := 980349075619088889932149

theorem tailTrace_1909223 : CollatzResearch.WordTrace tailWord_1909223 prefixEnd_1909223 980349075619088889932149 := by
  unfold tailWord_1909223
  simp only [CollatzResearch.WordTrace]
  refine ⟨69635083562218615173804323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46423389041479076782536215 69635083562218615173804323)
  ·
    refine ⟨104452625343327922760706485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69635083562218615173804323 104452625343327922760706485)
    ·
      refine ⟨9792433625936992758816233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104452625343327922760706485 9792433625936992758816233)
      ·
        refine ⟨7344325219452744569112175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9792433625936992758816233 7344325219452744569112175)
        ·
          refine ⟨11016487829179116853668263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344325219452744569112175 11016487829179116853668263)
          ·
            refine ⟨16524731743768675280502395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016487829179116853668263 16524731743768675280502395)
            ·
              refine ⟨24787097615653012920753593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16524731743768675280502395 24787097615653012920753593)
              ·
                refine ⟨18590323211739759690565195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24787097615653012920753593 18590323211739759690565195)
                ·
                  refine ⟨27885484817609639535847793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18590323211739759690565195 27885484817609639535847793)
                  ·
                    refine ⟨20914113613207229651885845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27885484817609639535847793 20914113613207229651885845)
                    ·
                      refine ⟨980349075619088889932149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20914113613207229651885845 980349075619088889932149)
                      ·
                        rfl

theorem cell23_1909223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1909223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909223 prefixEnd_1909223 := by exact prefixLift 1909223
  have htrace : WordTrace (prefixWord ++ tailWord_1909223) baseStart_1909223 baseEnd_1909223 := by
    simpa [prefixWord, tailWord_1909223, baseEnd_1909223] using wordTrace_append hprefix tailTrace_1909223
  have hstable : (prefixWord ++ tailWord_1909223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909223).length < 2 ^ (prefixWord ++ tailWord_1909223).sum := by decide
  have hdescent : baseEnd_1909223 < baseStart_1909223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909240 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 1, 5, 2]
def baseStart_1909240 : Nat := 118140960795 + 1909240 * 2 ^ 59
def prefixEnd_1909240 : Nat := 4983230072969 + 3 ^ 40 * 1909240 * 2
def baseEnd_1909240 : Nat := 980357804790215323419571

theorem tailTrace_1909240 : CollatzResearch.WordTrace tailWord_1909240 prefixEnd_1909240 980357804790215323419571 := by
  unfold tailWord_1909240
  simp only [CollatzResearch.WordTrace]
  refine ⟨34817851801578513538586587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46423802402104684718115449 34817851801578513538586587)
  ·
    refine ⟨52226777702367770307879881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34817851801578513538586587 52226777702367770307879881)
    ·
      refine ⟨39170083276775827730909911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52226777702367770307879881 39170083276775827730909911)
      ·
        refine ⟨58755124915163741596364867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39170083276775827730909911 58755124915163741596364867)
        ·
          refine ⟨88132687372745612394547301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58755124915163741596364867 88132687372745612394547301)
          ·
            refine ⟨16524878882389802323977619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88132687372745612394547301 16524878882389802323977619)
            ·
              refine ⟨24787318323584703485966429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16524878882389802323977619 24787318323584703485966429)
              ·
                refine ⟨9295244371344263807237411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24787318323584703485966429 9295244371344263807237411)
                ·
                  refine ⟨13942866557016395710856117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9295244371344263807237411 13942866557016395710856117)
                  ·
                    refine ⟨1307143739720287097892761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13942866557016395710856117 1307143739720287097892761)
                    ·
                      refine ⟨980357804790215323419571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307143739720287097892761 980357804790215323419571)
                      ·
                        rfl

theorem cell23_1909240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_1909240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909240 prefixEnd_1909240 := by exact prefixLift 1909240
  have htrace : WordTrace (prefixWord ++ tailWord_1909240) baseStart_1909240 baseEnd_1909240 := by
    simpa [prefixWord, tailWord_1909240, baseEnd_1909240] using wordTrace_append hprefix tailTrace_1909240
  have hstable : (prefixWord ++ tailWord_1909240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909240).length < 2 ^ (prefixWord ++ tailWord_1909240).sum := by decide
  have hdescent : baseEnd_1909240 < baseStart_1909240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909254 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1909254 : Nat := 118140960795 + 1909254 * 2 ^ 59
def prefixEnd_1909254 : Nat := 4983230072969 + 3 ^ 40 * 1909254 * 2
def baseEnd_1909254 : Nat := 108929443724375363182723

theorem tailTrace_1909254 : CollatzResearch.WordTrace tailWord_1909254 prefixEnd_1909254 108929443724375363182723 := by
  unfold tailWord_1909254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176131694534572108380713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46424142816737538312121877 2176131694534572108380713)
  ·
    refine ⟨1632098770900929081285535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2176131694534572108380713 1632098770900929081285535)
    ·
      refine ⟨2448148156351393621928303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632098770900929081285535 2448148156351393621928303)
      ·
        refine ⟨3672222234527090432892455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448148156351393621928303 3672222234527090432892455)
        ·
          refine ⟨5508333351790635649338683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672222234527090432892455 5508333351790635649338683)
          ·
            refine ⟨8262500027685953474008025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5508333351790635649338683 8262500027685953474008025)
            ·
              refine ⟨6196875020764465105506019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8262500027685953474008025 6196875020764465105506019)
              ·
                refine ⟨9295312531146697658259029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196875020764465105506019 9295312531146697658259029)
                ·
                  refine ⟨108929443724375363182723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9295312531146697658259029 108929443724375363182723)
                  ·
                    rfl

theorem cell23_1909254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1909254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909254 prefixEnd_1909254 := by exact prefixLift 1909254
  have htrace : WordTrace (prefixWord ++ tailWord_1909254) baseStart_1909254 baseEnd_1909254 := by
    simpa [prefixWord, tailWord_1909254, baseEnd_1909254] using wordTrace_append hprefix tailTrace_1909254
  have hstable : (prefixWord ++ tailWord_1909254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909254).length < 2 ^ (prefixWord ++ tailWord_1909254).sum := by decide
  have hdescent : baseEnd_1909254 < baseStart_1909254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909271 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 6]
def baseStart_1909271 : Nat := 118140960795 + 1909271 * 2 ^ 59
def prefixEnd_1909271 : Nat := 4983230072969 + 3 ^ 40 * 1909271 * 2
def baseEnd_1909271 : Nat := 108930413632278300236881

theorem tailTrace_1909271 : CollatzResearch.WordTrace tailWord_1909271 prefixEnd_1909271 108930413632278300236881 := by
  unfold tailWord_1909271
  simp only [CollatzResearch.WordTrace]
  refine ⟨69636834266044719371551667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46424556177363146247701111 69636834266044719371551667)
  ·
    refine ⟨104455251399067079057327501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69636834266044719371551667 104455251399067079057327501)
    ·
      refine ⟨39170719274650154646497813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104455251399067079057327501 39170719274650154646497813)
      ·
        refine ⟨1836127465999225999054585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39170719274650154646497813 1836127465999225999054585)
        ·
          refine ⟨1377095599499419499290939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836127465999225999054585 1377095599499419499290939)
          ·
            refine ⟨2065643399249129248936409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377095599499419499290939 2065643399249129248936409)
            ·
              refine ⟨1549232549436846936702307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065643399249129248936409 1549232549436846936702307)
              ·
                refine ⟨2323848824155270405053461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549232549436846936702307 2323848824155270405053461)
                ·
                  refine ⟨108930413632278300236881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2323848824155270405053461 108930413632278300236881)
                  ·
                    rfl

theorem cell23_1909271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 6].length) (baseStart_1909271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909271 prefixEnd_1909271 := by exact prefixLift 1909271
  have htrace : WordTrace (prefixWord ++ tailWord_1909271) baseStart_1909271 baseEnd_1909271 := by
    simpa [prefixWord, tailWord_1909271, baseEnd_1909271] using wordTrace_append hprefix tailTrace_1909271
  have hstable : (prefixWord ++ tailWord_1909271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909271).length < 2 ^ (prefixWord ++ tailWord_1909271).sum := by decide
  have hdescent : baseEnd_1909271 < baseStart_1909271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909310 : List Nat := [4, 2, 1, 4, 12]
def baseStart_1909310 : Nat := 118140960795 + 1909310 * 2 ^ 59
def prefixEnd_1909310 : Nat := 4983230072969 + 3 ^ 40 * 1909310 * 2
def baseEnd_1909310 : Nat := 1344847391544622838881

theorem tailTrace_1909310 : CollatzResearch.WordTrace tailWord_1909310 prefixEnd_1909310 1344847391544622838881 := by
  unfold tailWord_1909310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8704782089112928629027673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46425504475268952688147589 8704782089112928629027673)
  ·
    refine ⟨6528586566834696471770755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8704782089112928629027673 6528586566834696471770755)
    ·
      refine ⟨9792879850252044707656133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6528586566834696471770755 9792879850252044707656133)
      ·
        refine ⟨1836164971922258382685525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9792879850252044707656133 1836164971922258382685525)
        ·
          refine ⟨1344847391544622838881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1836164971922258382685525 1344847391544622838881)
          ·
            rfl

theorem cell23_1909310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 12].length) (baseStart_1909310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909310 prefixEnd_1909310 := by exact prefixLift 1909310
  have htrace : WordTrace (prefixWord ++ tailWord_1909310) baseStart_1909310 baseEnd_1909310 := by
    simpa [prefixWord, tailWord_1909310, baseEnd_1909310] using wordTrace_append hprefix tailTrace_1909310
  have hstable : (prefixWord ++ tailWord_1909310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909310).length < 2 ^ (prefixWord ++ tailWord_1909310).sum := by decide
  have hdescent : baseEnd_1909310 < baseStart_1909310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909323 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 2, 7]
def baseStart_1909323 : Nat := 118140960795 + 1909323 * 2 ^ 59
def prefixEnd_1909323 : Nat := 4983230072969 + 3 ^ 40 * 1909323 * 2
def baseEnd_1909323 : Nat := 326800141228179499560563

theorem tailTrace_1909323 : CollatzResearch.WordTrace tailWord_1909323 prefixEnd_1909323 326800141228179499560563 := by
  unfold tailWord_1909323
  simp only [CollatzResearch.WordTrace]
  refine ⟨69638730861856332252444623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46425820574570888168296415 69638730861856332252444623)
  ·
    refine ⟨104458096292784498378666935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69638730861856332252444623 104458096292784498378666935)
    ·
      refine ⟨156687144439176747568000403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104458096292784498378666935 156687144439176747568000403)
      ·
        refine ⟨235030716658765121352000605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156687144439176747568000403 235030716658765121352000605)
        ·
          refine ⟨88136518747036920507000227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235030716658765121352000605 88136518747036920507000227)
          ·
            refine ⟨132204778120555380760500341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88136518747036920507000227 132204778120555380760500341)
            ·
              refine ⟨12394197948802066946296907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132204778120555380760500341 12394197948802066946296907)
              ·
                refine ⟨18591296923203100419445361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12394197948802066946296907 18591296923203100419445361)
                ·
                  refine ⟨13943472692402325314584021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18591296923203100419445361 13943472692402325314584021)
                  ·
                    refine ⟨326800141228179499560563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13943472692402325314584021 326800141228179499560563)
                    ·
                      rfl

theorem cell23_1909323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_1909323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909323 prefixEnd_1909323 := by exact prefixLift 1909323
  have htrace : WordTrace (prefixWord ++ tailWord_1909323) baseStart_1909323 baseEnd_1909323 := by
    simpa [prefixWord, tailWord_1909323, baseEnd_1909323] using wordTrace_append hprefix tailTrace_1909323
  have hstable : (prefixWord ++ tailWord_1909323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909323).length < 2 ^ (prefixWord ++ tailWord_1909323).sum := by decide
  have hdescent : baseEnd_1909323 < baseStart_1909323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909342 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1909342 : Nat := 118140960795 + 1909342 * 2 ^ 59
def prefixEnd_1909342 : Nat := 4983230072969 + 3 ^ 40 * 1909342 * 2
def baseEnd_1909342 : Nat := 980410179816973924344103

theorem tailTrace_1909342 : CollatzResearch.WordTrace tailWord_1909342 prefixEnd_1909342 980410179816973924344103 := by
  unfold tailWord_1909342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8704927981098437312173285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46426282565858332331590853 8704927981098437312173285)
  ·
    refine ⟨1632173996455956996032491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8704927981098437312173285 1632173996455956996032491)
    ·
      refine ⟨2448260994683935494048737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632173996455956996032491 2448260994683935494048737)
      ·
        refine ⟨1836195746012951620536553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2448260994683935494048737 1836195746012951620536553)
        ·
          refine ⟨1377146809509713715402415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836195746012951620536553 1377146809509713715402415)
          ·
            refine ⟨2065720214264570573103623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377146809509713715402415 2065720214264570573103623)
            ·
              refine ⟨3098580321396855859655435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065720214264570573103623 3098580321396855859655435)
              ·
                refine ⟨4647870482095283789483153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098580321396855859655435 4647870482095283789483153)
                ·
                  refine ⟨3485902861571462842112365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647870482095283789483153 3485902861571462842112365)
                  ·
                    refine ⟨1307213573089298565792137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485902861571462842112365 1307213573089298565792137)
                    ·
                      refine ⟨980410179816973924344103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307213573089298565792137 980410179816973924344103)
                      ·
                        rfl

theorem cell23_1909342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1909342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909342 prefixEnd_1909342 := by exact prefixLift 1909342
  have htrace : WordTrace (prefixWord ++ tailWord_1909342) baseStart_1909342 baseEnd_1909342 := by
    simpa [prefixWord, tailWord_1909342, baseEnd_1909342] using wordTrace_append hprefix tailTrace_1909342
  have hstable : (prefixWord ++ tailWord_1909342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909342).length < 2 ^ (prefixWord ++ tailWord_1909342).sum := by decide
  have hdescent : baseEnd_1909342 < baseStart_1909342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909347 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 3, 3, 2]
def baseStart_1909347 : Nat := 118140960795 + 1909347 * 2 ^ 59
def prefixEnd_1909347 : Nat := 4983230072969 + 3 ^ 40 * 1909347 * 2
def baseEnd_1909347 : Nat := 980412747220246404781579

theorem tailTrace_1909347 : CollatzResearch.WordTrace tailWord_1909347 prefixEnd_1909347 980412747220246404781579 := by
  unfold tailWord_1909347
  simp only [CollatzResearch.WordTrace]
  refine ⟨69639606213769384351318295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46426404142512922900878863 69639606213769384351318295)
  ·
    refine ⟨104459409320654076526977443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69639606213769384351318295 104459409320654076526977443)
    ·
      refine ⟨156689113980981114790466165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104459409320654076526977443 156689113980981114790466165)
      ·
        refine ⟨14689604435716979511606203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156689113980981114790466165 14689604435716979511606203)
        ·
          refine ⟨22034406653575469267409305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14689604435716979511606203 22034406653575469267409305)
          ·
            refine ⟨16525804990181601950556979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22034406653575469267409305 16525804990181601950556979)
            ·
              refine ⟨24788707485272402925835469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16525804990181601950556979 24788707485272402925835469)
              ·
                refine ⟨9295765306977151097188301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24788707485272402925835469 9295765306977151097188301)
                ·
                  refine ⟨3485911990116431661445613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9295765306977151097188301 3485911990116431661445613)
                  ·
                    refine ⟨1307216996293661873042105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485911990116431661445613 1307216996293661873042105)
                    ·
                      refine ⟨980412747220246404781579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1307216996293661873042105 980412747220246404781579)
                      ·
                        rfl

theorem cell23_1909347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_1909347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909347 prefixEnd_1909347 := by exact prefixLift 1909347
  have htrace : WordTrace (prefixWord ++ tailWord_1909347) baseStart_1909347 baseEnd_1909347 := by
    simpa [prefixWord, tailWord_1909347, baseEnd_1909347] using wordTrace_append hprefix tailTrace_1909347
  have hstable : (prefixWord ++ tailWord_1909347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909347).length < 2 ^ (prefixWord ++ tailWord_1909347).sum := by decide
  have hdescent : baseEnd_1909347 < baseStart_1909347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909353 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 3, 8]
def baseStart_1909353 : Nat := 118140960795 + 1909353 * 2 ^ 59
def prefixEnd_1909353 : Nat := 4983230072969 + 3 ^ 40 * 1909353 * 2
def baseEnd_1909353 : Nat := 326805276034724460435517

theorem tailTrace_1909353 : CollatzResearch.WordTrace tailWord_1909353 prefixEnd_1909353 326805276034724460435517 := by
  unfold tailWord_1909353
  simp only [CollatzResearch.WordTrace]
  refine ⟨69639825051747647376036713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46426550034498431584024475 69639825051747647376036713)
  ·
    refine ⟨52229868788810735532027535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69639825051747647376036713 52229868788810735532027535)
    ·
      refine ⟨78344803183216103298041303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52229868788810735532027535 78344803183216103298041303)
      ·
        refine ⟨117517204774824154947061955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78344803183216103298041303 117517204774824154947061955)
        ·
          refine ⟨176275807162236232420592933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117517204774824154947061955 176275807162236232420592933)
          ·
            refine ⟨33051713842919293578861175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176275807162236232420592933 33051713842919293578861175)
            ·
              refine ⟨49577570764378940368291763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33051713842919293578861175 49577570764378940368291763)
              ·
                refine ⟨74366356146568410552437645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49577570764378940368291763 74366356146568410552437645)
                ·
                  refine ⟨27887383554963153957164117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74366356146568410552437645 27887383554963153957164117)
                  ·
                    refine ⟨326805276034724460435517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27887383554963153957164117 326805276034724460435517)
                    ·
                      rfl

theorem cell23_1909353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_1909353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909353 prefixEnd_1909353 := by exact prefixLift 1909353
  have htrace : WordTrace (prefixWord ++ tailWord_1909353) baseStart_1909353 baseEnd_1909353 := by
    simpa [prefixWord, tailWord_1909353, baseEnd_1909353] using wordTrace_append hprefix tailTrace_1909353
  have hstable : (prefixWord ++ tailWord_1909353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909353).length < 2 ^ (prefixWord ++ tailWord_1909353).sum := by decide
  have hdescent : baseEnd_1909353 < baseStart_1909353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909400 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 7]
def baseStart_1909400 : Nat := 118140960795 + 1909400 * 2 ^ 59
def prefixEnd_1909400 : Nat := 4983230072969 + 3 ^ 40 * 1909400 * 2
def baseEnd_1909400 : Nat := 108937773521659410824315

theorem tailTrace_1909400 : CollatzResearch.WordTrace tailWord_1909400 prefixEnd_1909400 108937773521659410824315 := by
  unfold tailWord_1909400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34820769641288687201498827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46427692855051582935331769 34820769641288687201498827)
  ·
    refine ⟨52231154461933030802248241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34820769641288687201498827 52231154461933030802248241)
    ·
      refine ⟨39173365846449773101686181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52231154461933030802248241 39173365846449773101686181)
      ·
        refine ⟨7345006096209332456566159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39173365846449773101686181 7345006096209332456566159)
        ·
          refine ⟨11017509144313998684849239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345006096209332456566159 11017509144313998684849239)
          ·
            refine ⟨16526263716470998027273859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017509144313998684849239 16526263716470998027273859)
            ·
              refine ⟨24789395574706497040910789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16526263716470998027273859 24789395574706497040910789)
              ·
                refine ⟨4648011670257468195170773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24789395574706497040910789 4648011670257468195170773)
                ·
                  refine ⟨108937773521659410824315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4648011670257468195170773 108937773521659410824315)
                  ·
                    rfl

theorem cell23_1909400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 7].length) (baseStart_1909400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909400 prefixEnd_1909400 := by exact prefixLift 1909400
  have htrace : WordTrace (prefixWord ++ tailWord_1909400) baseStart_1909400 baseEnd_1909400 := by
    simpa [prefixWord, tailWord_1909400, baseEnd_1909400] using wordTrace_append hprefix tailTrace_1909400
  have hstable : (prefixWord ++ tailWord_1909400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909400).length < 2 ^ (prefixWord ++ tailWord_1909400).sum := by decide
  have hdescent : baseEnd_1909400 < baseStart_1909400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909434 : List Nat := [3, 1, 1, 1, 2, 3, 5, 2, 5]
def baseStart_1909434 : Nat := 118140960795 + 1909434 * 2 ^ 59
def prefixEnd_1909434 : Nat := 4983230072969 + 3 ^ 40 * 1909434 * 2
def baseEnd_1909434 : Nat := 108939713337465284932631

theorem tailTrace_1909434 : CollatzResearch.WordTrace tailWord_1909434 prefixEnd_1909434 108939713337465284932631 := by
  unfold tailWord_1909434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17410694841113549552433839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46428519576302798806490237 17410694841113549552433839)
  ·
    refine ⟨26116042261670324328650759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17410694841113549552433839 26116042261670324328650759)
    ·
      refine ⟨39174063392505486492976139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26116042261670324328650759 39174063392505486492976139)
      ·
        refine ⟨58761095088758229739464209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39174063392505486492976139 58761095088758229739464209)
        ·
          refine ⟨44070821316568672304598157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58761095088758229739464209 44070821316568672304598157)
          ·
            refine ⟨16526557993713252114224309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44070821316568672304598157 16526557993713252114224309)
            ·
              refine ⟨1549364811910617385708529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16526557993713252114224309 1549364811910617385708529)
              ·
                refine ⟨1162023608932963039281397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549364811910617385708529 1162023608932963039281397)
                ·
                  refine ⟨108939713337465284932631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1162023608932963039281397 108939713337465284932631)
                  ·
                    rfl

theorem cell23_1909434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_1909434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909434 prefixEnd_1909434 := by exact prefixLift 1909434
  have htrace : WordTrace (prefixWord ++ tailWord_1909434) baseStart_1909434 baseEnd_1909434 := by
    simpa [prefixWord, tailWord_1909434, baseEnd_1909434] using wordTrace_append hprefix tailTrace_1909434
  have hstable : (prefixWord ++ tailWord_1909434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909434).length < 2 ^ (prefixWord ++ tailWord_1909434).sum := by decide
  have hdescent : baseEnd_1909434 < baseStart_1909434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909440 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1909440 : Nat := 118140960795 + 1909440 * 2 ^ 59
def prefixEnd_1909440 : Nat := 4983230072969 + 3 ^ 40 * 1909440 * 2
def baseEnd_1909440 : Nat := 980460500921114540918651

theorem tailTrace_1909440 : CollatzResearch.WordTrace tailWord_1909440 prefixEnd_1909440 980460500921114540918651 := by
  unfold tailWord_1909440
  simp only [CollatzResearch.WordTrace]
  refine ⟨34821499101216230617226887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46428665468288307489635849 34821499101216230617226887)
  ·
    refine ⟨52232248651824345925840331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34821499101216230617226887 52232248651824345925840331)
    ·
      refine ⟨78348372977736518888760497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52232248651824345925840331 78348372977736518888760497)
      ·
        refine ⟨58761279733302389166570373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78348372977736518888760497 58761279733302389166570373)
        ·
          refine ⟨11017739949994197968731945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58761279733302389166570373 11017739949994197968731945)
          ·
            refine ⟨8263304962495648476548959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11017739949994197968731945 8263304962495648476548959)
            ·
              refine ⟨12394957443743472714823439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8263304962495648476548959 12394957443743472714823439)
              ·
                refine ⟨18592436165615209072235159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12394957443743472714823439 18592436165615209072235159)
                ·
                  refine ⟨27888654248422813608352739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18592436165615209072235159 27888654248422813608352739)
                  ·
                    refine ⟨41832981372634220412529109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27888654248422813608352739 41832981372634220412529109)
                    ·
                      refine ⟨980460500921114540918651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41832981372634220412529109 980460500921114540918651)
                      ·
                        rfl

theorem cell23_1909440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1909440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909440 prefixEnd_1909440 := by exact prefixLift 1909440
  have htrace : WordTrace (prefixWord ++ tailWord_1909440) baseStart_1909440 baseEnd_1909440 := by
    simpa [prefixWord, tailWord_1909440, baseEnd_1909440] using wordTrace_append hprefix tailTrace_1909440
  have hstable : (prefixWord ++ tailWord_1909440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909440).length < 2 ^ (prefixWord ++ tailWord_1909440).sum := by decide
  have hdescent : baseEnd_1909440 < baseStart_1909440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909494 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1909494 : Nat := 118140960795 + 1909494 * 2 ^ 59
def prefixEnd_1909494 : Nat := 4983230072969 + 3 ^ 40 * 1909494 * 2
def baseEnd_1909494 : Nat := 326829409625485776547801

theorem tailTrace_1909494 : CollatzResearch.WordTrace tailWord_1909494 prefixEnd_1909494 326829409625485776547801 := by
  unfold tailWord_1909494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352810484014801778557471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46429978496157885637946357 4352810484014801778557471)
  ·
    refine ⟨6529215726022202667836207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4352810484014801778557471 6529215726022202667836207)
    ·
      refine ⟨9793823589033304001754311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6529215726022202667836207 9793823589033304001754311)
      ·
        refine ⟨14690735383549956002631467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9793823589033304001754311 14690735383549956002631467)
        ·
          refine ⟨22036103075324934003947201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14690735383549956002631467 22036103075324934003947201)
          ·
            refine ⟨16527077306493700502960401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22036103075324934003947201 16527077306493700502960401)
            ·
              refine ⟨12395307979870275377220301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16527077306493700502960401 12395307979870275377220301)
              ·
                refine ⟨4648240492451353266457613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12395307979870275377220301 4648240492451353266457613)
                ·
                  refine ⟨1743090184669257474921605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4648240492451353266457613 1743090184669257474921605)
                  ·
                    refine ⟨326829409625485776547801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1743090184669257474921605 326829409625485776547801)
                    ·
                      rfl

theorem cell23_1909494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1909494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909494 prefixEnd_1909494 := by exact prefixLift 1909494
  have htrace : WordTrace (prefixWord ++ tailWord_1909494) baseStart_1909494 baseEnd_1909494 := by
    simpa [prefixWord, tailWord_1909494, baseEnd_1909494] using wordTrace_append hprefix tailTrace_1909494
  have hstable : (prefixWord ++ tailWord_1909494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909494).length < 2 ^ (prefixWord ++ tailWord_1909494).sum := by decide
  have hdescent : baseEnd_1909494 < baseStart_1909494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909558 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1909558 : Nat := 118140960795 + 1909558 * 2 ^ 59
def prefixEnd_1909558 : Nat := 4983230072969 + 3 ^ 40 * 1909558 * 2
def baseEnd_1909558 : Nat := 108946787959816119915901

theorem tailTrace_1909558 : CollatzResearch.WordTrace tailWord_1909558 prefixEnd_1909558 108946787959816119915901 := by
  unfold tailWord_1909558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352956376000310461703083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46431534677336644924832885 4352956376000310461703083)
  ·
    refine ⟨6529434564000465692554625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4352956376000310461703083 6529434564000465692554625)
    ·
      refine ⟨4897075923000349269415969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6529434564000465692554625 4897075923000349269415969)
      ·
        refine ⟨3672806942250261952061977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4897075923000349269415969 3672806942250261952061977)
        ·
          refine ⟨2754605206687696464046483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3672806942250261952061977 2754605206687696464046483)
          ·
            refine ⟨4131907810031544696069725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754605206687696464046483 4131907810031544696069725)
            ·
              refine ⟨1549465428761829261026147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4131907810031544696069725 1549465428761829261026147)
              ·
                refine ⟨2324198143142743891539221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549465428761829261026147 2324198143142743891539221)
                ·
                  refine ⟨108946787959816119915901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2324198143142743891539221 108946787959816119915901)
                  ·
                    rfl

theorem cell23_1909558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1909558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909558 prefixEnd_1909558 := by exact prefixLift 1909558
  have htrace : WordTrace (prefixWord ++ tailWord_1909558) baseStart_1909558 baseEnd_1909558 := by
    simpa [prefixWord, tailWord_1909558, baseEnd_1909558] using wordTrace_append hprefix tailTrace_1909558
  have hstable : (prefixWord ++ tailWord_1909558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909558).length < 2 ^ (prefixWord ++ tailWord_1909558).sum := by decide
  have hdescent : baseEnd_1909558 < baseStart_1909558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909585 : List Nat := [1, 2, 2, 1, 6, 2, 1, 3, 1, 1, 3]
def baseStart_1909585 : Nat := 118140960795 + 1909585 * 2 ^ 59
def prefixEnd_1909585 : Nat := 4983230072969 + 3 ^ 40 * 1909585 * 2
def baseEnd_1909585 : Nat := 980534955616016473605485

theorem tailTrace_1909585 : CollatzResearch.WordTrace tailWord_1909585 prefixEnd_1909585 980534955616016473605485 := by
  unfold tailWord_1909585
  simp only [CollatzResearch.WordTrace]
  refine ⟨69648286786907150998482209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46432191191271433998988139 69648286786907150998482209)
  ·
    refine ⟨52236215090180363248861657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69648286786907150998482209 52236215090180363248861657)
    ·
      refine ⟨39177161317635272436646243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52236215090180363248861657 39177161317635272436646243)
      ·
        refine ⟨58765741976452908654969365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39177161317635272436646243 58765741976452908654969365)
        ·
          refine ⟨2754644155146230093201689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58765741976452908654969365 2754644155146230093201689)
          ·
            refine ⟨2065983116359672569901267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754644155146230093201689 2065983116359672569901267)
            ·
              refine ⟨3098974674539508854851901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065983116359672569901267 3098974674539508854851901)
              ·
                refine ⟨1162115502952315820569463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3098974674539508854851901 1162115502952315820569463)
                ·
                  refine ⟨1743173254428473730854195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162115502952315820569463 1743173254428473730854195)
                  ·
                    refine ⟨2614759881642710596281293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1743173254428473730854195 2614759881642710596281293)
                    ·
                      refine ⟨980534955616016473605485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2614759881642710596281293 980534955616016473605485)
                      ·
                        rfl

theorem cell23_1909585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_1909585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909585 prefixEnd_1909585 := by exact prefixLift 1909585
  have htrace : WordTrace (prefixWord ++ tailWord_1909585) baseStart_1909585 baseEnd_1909585 := by
    simpa [prefixWord, tailWord_1909585, baseEnd_1909585] using wordTrace_append hprefix tailTrace_1909585
  have hstable : (prefixWord ++ tailWord_1909585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909585).length < 2 ^ (prefixWord ++ tailWord_1909585).sum := by decide
  have hdescent : baseEnd_1909585 < baseStart_1909585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909587 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4]
def baseStart_1909587 : Nat := 118140960795 + 1909587 * 2 ^ 59
def prefixEnd_1909587 : Nat := 4983230072969 + 3 ^ 40 * 1909587 * 2
def baseEnd_1909587 : Nat := 980535982577325465780475

theorem tailTrace_1909587 : CollatzResearch.WordTrace tailWord_1909587 prefixEnd_1909587 980535982577325465780475 := by
  unfold tailWord_1909587
  simp only [CollatzResearch.WordTrace]
  refine ⟨69648359732899905340055015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46432239821933270226703343 69648359732899905340055015)
  ·
    refine ⟨104472539599349858010082523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69648359732899905340055015 104472539599349858010082523)
    ·
      refine ⟨156708809399024787015123785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104472539599349858010082523 156708809399024787015123785)
      ·
        refine ⟨117531607049268590261342839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156708809399024787015123785 117531607049268590261342839)
        ·
          refine ⟨176297410573902885392014259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117531607049268590261342839 176297410573902885392014259)
          ·
            refine ⟨264446115860854328088021389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176297410573902885392014259 264446115860854328088021389)
            ·
              refine ⟨99167293447820373033008021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264446115860854328088021389 99167293447820373033008021)
              ·
                refine ⟨4648466880366579985922251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99167293447820373033008021 4648466880366579985922251)
                ·
                  refine ⟨6972700320549869978883377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648466880366579985922251 6972700320549869978883377)
                  ·
                    refine ⟨5229525240412402484162533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6972700320549869978883377 5229525240412402484162533)
                    ·
                      refine ⟨980535982577325465780475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5229525240412402484162533 980535982577325465780475)
                      ·
                        rfl

theorem cell23_1909587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_1909587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909587 prefixEnd_1909587 := by exact prefixLift 1909587
  have htrace : WordTrace (prefixWord ++ tailWord_1909587) baseStart_1909587 baseEnd_1909587 := by
    simpa [prefixWord, tailWord_1909587, baseEnd_1909587] using wordTrace_append hprefix tailTrace_1909587
  have hstable : (prefixWord ++ tailWord_1909587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909587).length < 2 ^ (prefixWord ++ tailWord_1909587).sum := by decide
  have hdescent : baseEnd_1909587 < baseStart_1909587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909594 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_1909594 : Nat := 118140960795 + 1909594 * 2 ^ 59
def prefixEnd_1909594 : Nat := 4983230072969 + 3 ^ 40 * 1909594 * 2
def baseEnd_1909594 : Nat := 980539576941906938392943

theorem tailTrace_1909594 : CollatzResearch.WordTrace tailWord_1909594 prefixEnd_1909594 980539576941906938392943 := by
  unfold tailWord_1909594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412153760968636383889959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46432410029249697023706557 17412153760968636383889959)
  ·
    refine ⟨26118230641452954575834939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17412153760968636383889959 26118230641452954575834939)
    ·
      refine ⟨39177345962179431863752409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26118230641452954575834939 39177345962179431863752409)
      ·
        refine ⟨29383009471634573897814307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39177345962179431863752409 29383009471634573897814307)
        ·
          refine ⟨44074514207451860846721461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29383009471634573897814307 44074514207451860846721461)
          ·
            refine ⟨4131985706948611954380137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44074514207451860846721461 4131985706948611954380137)
            ·
              refine ⟨3098989280211458965785103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131985706948611954380137 3098989280211458965785103)
              ·
                refine ⟨4648483920317188448677655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098989280211458965785103 4648483920317188448677655)
                ·
                  refine ⟨6972725880475782673016483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648483920317188448677655 6972725880475782673016483)
                  ·
                    refine ⟨10459088820713674009524725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6972725880475782673016483 10459088820713674009524725)
                    ·
                      refine ⟨980539576941906938392943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10459088820713674009524725 980539576941906938392943)
                      ·
                        rfl

theorem cell23_1909594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_1909594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1909594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1909594 prefixEnd_1909594 := by exact prefixLift 1909594
  have htrace : WordTrace (prefixWord ++ tailWord_1909594) baseStart_1909594 baseEnd_1909594 := by
    simpa [prefixWord, tailWord_1909594, baseEnd_1909594] using wordTrace_append hprefix tailTrace_1909594
  have hstable : (prefixWord ++ tailWord_1909594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909594).length < 2 ^ (prefixWord ++ tailWord_1909594).sum := by decide
  have hdescent : baseEnd_1909594 < baseStart_1909594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
