import V185TrunkScan23Chunk0377

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2234778 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2234778 : Nat := 118140960795 + 2234778 * 2 ^ 59
def prefixEnd_2234778 : Nat := 4983230072969 + 3 ^ 40 * 2234778 * 2
def baseEnd_2234778 : Nat := 1147515270093562654497449

theorem tailTrace_2234778 : CollatzResearch.WordTrace tailWord_2234778 prefixEnd_2234778 1147515270093562654497449 := by
  unfold tailWord_2234778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20377262474447112635308247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54339366598525633694155325 20377262474447112635308247)
  ·
    refine ⟨30565893711670668952962371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20377262474447112635308247 30565893711670668952962371)
    ·
      refine ⟨45848840567506003429443557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30565893711670668952962371 45848840567506003429443557)
      ·
        refine ⟨8596657606407375643020667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45848840567506003429443557 8596657606407375643020667)
        ·
          refine ⟨12894986409611063464531001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8596657606407375643020667 12894986409611063464531001)
          ·
            refine ⟨9671239807208297598398251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12894986409611063464531001 9671239807208297598398251)
            ·
              refine ⟨14506859710812446397597377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9671239807208297598398251 14506859710812446397597377)
              ·
                refine ⟨10880144783109334798198033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14506859710812446397597377 10880144783109334798198033)
                ·
                  refine ⟨8160108587332001098648525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10880144783109334798198033 8160108587332001098648525)
                  ·
                    refine ⟨3060040720249500411993197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8160108587332001098648525 3060040720249500411993197)
                    ·
                      refine ⟨1147515270093562654497449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060040720249500411993197 1147515270093562654497449)
                      ·
                        rfl

theorem cell23_2234778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2234778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234778 prefixEnd_2234778 := by exact prefixLift 2234778
  have htrace : WordTrace (prefixWord ++ tailWord_2234778) baseStart_2234778 baseEnd_2234778 := by
    simpa [prefixWord, tailWord_2234778, baseEnd_2234778] using wordTrace_append hprefix tailTrace_2234778
  have hstable : (prefixWord ++ tailWord_2234778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234778).length < 2 ^ (prefixWord ++ tailWord_2234778).sum := by decide
  have hdescent : baseEnd_2234778 < baseStart_2234778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234785 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 7]
def baseStart_2234785 : Nat := 118140960795 + 2234785 * 2 ^ 59
def prefixEnd_2234785 : Nat := 4983230072969 + 3 ^ 40 * 2234785 * 2
def baseEnd_2234785 : Nat := 127502096050904903012213

theorem tailTrace_2234785 : CollatzResearch.WordTrace tailWord_2234785 prefixEnd_2234785 127502096050904903012213 := by
  unfold tailWord_2234785
  simp only [CollatzResearch.WordTrace]
  refine ⟨81509305208763090736737809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54339536805842060491158539 81509305208763090736737809)
  ·
    refine ⟨61131978906572318052553357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81509305208763090736737809 61131978906572318052553357)
    ·
      refine ⟨22924492089964619269707509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61131978906572318052553357 22924492089964619269707509)
      ·
        refine ⟨2149171133434183056535079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22924492089964619269707509 2149171133434183056535079)
        ·
          refine ⟨3223756700151274584802619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149171133434183056535079 3223756700151274584802619)
          ·
            refine ⟨4835635050226911877203929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223756700151274584802619 4835635050226911877203929)
            ·
              refine ⟨3626726287670183907902947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835635050226911877203929 3626726287670183907902947)
              ·
                refine ⟨5440089431505275861854421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626726287670183907902947 5440089431505275861854421)
                ·
                  refine ⟨127502096050904903012213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5440089431505275861854421 127502096050904903012213)
                  ·
                    rfl

theorem cell23_2234785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 7].length) (baseStart_2234785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234785 prefixEnd_2234785 := by exact prefixLift 2234785
  have htrace : WordTrace (prefixWord ++ tailWord_2234785) baseStart_2234785 baseEnd_2234785 := by
    simpa [prefixWord, tailWord_2234785, baseEnd_2234785] using wordTrace_append hprefix tailTrace_2234785
  have hstable : (prefixWord ++ tailWord_2234785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234785).length < 2 ^ (prefixWord ++ tailWord_2234785).sum := by decide
  have hdescent : baseEnd_2234785 < baseStart_2234785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234788 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_2234788 : Nat := 118140960795 + 2234788 * 2 ^ 59
def prefixEnd_2234788 : Nat := 4983230072969 + 3 ^ 40 * 2234788 * 2
def baseEnd_2234788 : Nat := 1147520404900107615372403

theorem tailTrace_2234788 : CollatzResearch.WordTrace tailWord_2234788 prefixEnd_2234788 1147520404900107615372403 := by
  unfold tailWord_2234788
  simp only [CollatzResearch.WordTrace]
  refine ⟨40754707313876111124548509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54339609751834814832731345 40754707313876111124548509)
  ·
    refine ⟨15283015242703541671705691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40754707313876111124548509 15283015242703541671705691)
    ·
      refine ⟨22924522864055312507558537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15283015242703541671705691 22924522864055312507558537)
      ·
        refine ⟨17193392148041484380668903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22924522864055312507558537 17193392148041484380668903)
        ·
          refine ⟨25790088222062226571003355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17193392148041484380668903 25790088222062226571003355)
          ·
            refine ⟨38685132333093339856505033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25790088222062226571003355 38685132333093339856505033)
            ·
              refine ⟨29013849249820004892378775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38685132333093339856505033 29013849249820004892378775)
              ·
                refine ⟨43520773874730007338568163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29013849249820004892378775 43520773874730007338568163)
                ·
                  refine ⟨65281160812095011007852245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43520773874730007338568163 65281160812095011007852245)
                  ·
                    refine ⟨1530027206533476820496537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65281160812095011007852245 1530027206533476820496537)
                    ·
                      refine ⟨1147520404900107615372403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530027206533476820496537 1147520404900107615372403)
                      ·
                        rfl

theorem cell23_2234788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_2234788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234788 prefixEnd_2234788 := by exact prefixLift 2234788
  have htrace : WordTrace (prefixWord ++ tailWord_2234788) baseStart_2234788 baseEnd_2234788 := by
    simpa [prefixWord, tailWord_2234788, baseEnd_2234788] using wordTrace_append hprefix tailTrace_2234788
  have hstable : (prefixWord ++ tailWord_2234788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234788).length < 2 ^ (prefixWord ++ tailWord_2234788).sum := by decide
  have hdescent : baseEnd_2234788 < baseStart_2234788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234841 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 8]
def baseStart_2234841 : Nat := 118140960795 + 2234841 * 2 ^ 59
def prefixEnd_2234841 : Nat := 4983230072969 + 3 ^ 40 * 2234841 * 2
def baseEnd_2234841 : Nat := 127505291041643989778851

theorem tailTrace_2234841 : CollatzResearch.WordTrace tailWord_2234841 prefixEnd_2234841 127505291041643989778851 := by
  unfold tailWord_2234841
  simp only [CollatzResearch.WordTrace]
  refine ⟨81511347696560212300776377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54340898464373474867184251 81511347696560212300776377)
  ·
    refine ⟨61133510772420159225582283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81511347696560212300776377 61133510772420159225582283)
    ·
      refine ⟨91700266158630238838373425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61133510772420159225582283 91700266158630238838373425)
      ·
        refine ⟨68775199618972679128780069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91700266158630238838373425 68775199618972679128780069)
        ·
          refine ⟨12895349928557377336646263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68775199618972679128780069 12895349928557377336646263)
          ·
            refine ⟨19343024892836066004969395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12895349928557377336646263 19343024892836066004969395)
            ·
              refine ⟨29014537339254099007454093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19343024892836066004969395 29014537339254099007454093)
              ·
                refine ⟨10880451502220287127795285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29014537339254099007454093 10880451502220287127795285)
                ·
                  refine ⟨127505291041643989778851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10880451502220287127795285 127505291041643989778851)
                  ·
                    rfl

theorem cell23_2234841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_2234841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234841 prefixEnd_2234841 := by exact prefixLift 2234841
  have htrace : WordTrace (prefixWord ++ tailWord_2234841) baseStart_2234841 baseEnd_2234841 := by
    simpa [prefixWord, tailWord_2234841, baseEnd_2234841] using wordTrace_append hprefix tailTrace_2234841
  have hstable : (prefixWord ++ tailWord_2234841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234841).length < 2 ^ (prefixWord ++ tailWord_2234841).sum := by decide
  have hdescent : baseEnd_2234841 < baseStart_2234841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234959 : List Nat := [1, 1, 2, 1, 1, 2, 6, 4, 1, 2, 2]
def baseStart_2234959 : Nat := 118140960795 + 2234959 * 2 ^ 59
def prefixEnd_2234959 : Nat := 4983230072969 + 3 ^ 40 * 2234959 * 2
def baseEnd_2234959 : Nat := 1147608210092026446334117

theorem tailTrace_2234959 : CollatzResearch.WordTrace tailWord_2234959 prefixEnd_2234959 1147608210092026446334117 := by
  unfold tailWord_2234959
  simp only [CollatzResearch.WordTrace]
  refine ⟨81515651510132718453571931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54343767673421812302381287 81515651510132718453571931)
  ·
    refine ⟨122273477265199077680357897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81515651510132718453571931 122273477265199077680357897)
    ·
      refine ⟨91705107948899308260268423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122273477265199077680357897 91705107948899308260268423)
      ·
        refine ⟨137557661923348962390402635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91705107948899308260268423 137557661923348962390402635)
        ·
          refine ⟨206336492885023443585603953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137557661923348962390402635 206336492885023443585603953)
          ·
            refine ⟨154752369663767582689202965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206336492885023443585603953 154752369663767582689202965)
            ·
              refine ⟨7254017327989105438556389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 154752369663767582689202965 7254017327989105438556389)
              ·
                refine ⟨1360128248997957269729323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7254017327989105438556389 1360128248997957269729323)
                ·
                  refine ⟨2040192373496935904593985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360128248997957269729323 2040192373496935904593985)
                  ·
                    refine ⟨1530144280122701928445489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2040192373496935904593985 1530144280122701928445489)
                    ·
                      refine ⟨1147608210092026446334117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530144280122701928445489 1147608210092026446334117)
                      ·
                        rfl

theorem cell23_2234959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 2, 2].length) (baseStart_2234959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234959 prefixEnd_2234959 := by exact prefixLift 2234959
  have htrace : WordTrace (prefixWord ++ tailWord_2234959) baseStart_2234959 baseEnd_2234959 := by
    simpa [prefixWord, tailWord_2234959, baseEnd_2234959] using wordTrace_append hprefix tailTrace_2234959
  have hstable : (prefixWord ++ tailWord_2234959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234959).length < 2 ^ (prefixWord ++ tailWord_2234959).sum := by decide
  have hdescent : baseEnd_2234959 < baseStart_2234959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234988 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_2234988 : Nat := 118140960795 + 2234988 * 2 ^ 59
def prefixEnd_2234988 : Nat := 4983230072969 + 3 ^ 40 * 2234988 * 2
def baseEnd_2234988 : Nat := 1147623101031006832871483

theorem tailTrace_2234988 : CollatzResearch.WordTrace tailWord_2234988 prefixEnd_2234988 1147623101031006832871483 := by
  unfold tailWord_2234988
  simp only [CollatzResearch.WordTrace]
  refine ⟨40758354613513828203188809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54344472818018437604251745 40758354613513828203188809)
  ·
    refine ⟨30568765960135371152391607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40758354613513828203188809 30568765960135371152391607)
    ·
      refine ⟨45853148940203056728587411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30568765960135371152391607 45853148940203056728587411)
      ·
        refine ⟨68779723410304585092881117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45853148940203056728587411 68779723410304585092881117)
        ·
          refine ⟨25792396278864219409830419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68779723410304585092881117 25792396278864219409830419)
          ·
            refine ⟨38688594418296329114745629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25792396278864219409830419 38688594418296329114745629)
            ·
              refine ⟨14508222906861123418029611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38688594418296329114745629 14508222906861123418029611)
              ·
                refine ⟨21762334360291685127044417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14508222906861123418029611 21762334360291685127044417)
                ·
                  refine ⟨16321750770218763845283313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21762334360291685127044417 16321750770218763845283313)
                  ·
                    refine ⟨12241313077664072883962485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16321750770218763845283313 12241313077664072883962485)
                    ·
                      refine ⟨1147623101031006832871483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12241313077664072883962485 1147623101031006832871483)
                      ·
                        rfl

theorem cell23_2234988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_2234988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2234988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2234988 prefixEnd_2234988 := by exact prefixLift 2234988
  have htrace : WordTrace (prefixWord ++ tailWord_2234988) baseStart_2234988 baseEnd_2234988 := by
    simpa [prefixWord, tailWord_2234988, baseEnd_2234988] using wordTrace_append hprefix tailTrace_2234988
  have hstable : (prefixWord ++ tailWord_2234988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234988).length < 2 ^ (prefixWord ++ tailWord_2234988).sum := by decide
  have hdescent : baseEnd_2234988 < baseStart_2234988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235026 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_2235026 : Nat := 118140960795 + 2235026 * 2 ^ 59
def prefixEnd_2235026 : Nat := 4983230072969 + 3 ^ 40 * 2235026 * 2
def baseEnd_2235026 : Nat := 1147642613295877684196309

theorem tailTrace_2235026 : CollatzResearch.WordTrace tailWord_2235026 prefixEnd_2235026 1147642613295877684196309 := by
  unfold tailWord_2235026
  simp only [CollatzResearch.WordTrace]
  refine ⟨20379523800222497224065233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54345396800593325930840621 20379523800222497224065233)
  ·
    refine ⟨15284642850166872918048925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20379523800222497224065233 15284642850166872918048925)
    ·
      refine ⟨5731741068812577344268347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15284642850166872918048925 5731741068812577344268347)
      ·
        refine ⟨8597611603218866016402521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5731741068812577344268347 8597611603218866016402521)
        ·
          refine ⟨6448208702414149512301891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8597611603218866016402521 6448208702414149512301891)
          ·
            refine ⟨9672313053621224268452837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6448208702414149512301891 9672313053621224268452837)
            ·
              refine ⟨1813558697553979550334907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9672313053621224268452837 1813558697553979550334907)
              ·
                refine ⟨2720338046330969325502361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813558697553979550334907 2720338046330969325502361)
                ·
                  refine ⟨2040253534748226994126771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720338046330969325502361 2040253534748226994126771)
                  ·
                    refine ⟨3060380302122340491190157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040253534748226994126771 3060380302122340491190157)
                    ·
                      refine ⟨1147642613295877684196309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060380302122340491190157 1147642613295877684196309)
                      ·
                        rfl

theorem cell23_2235026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_2235026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235026 prefixEnd_2235026 := by exact prefixLift 2235026
  have htrace : WordTrace (prefixWord ++ tailWord_2235026) baseStart_2235026 baseEnd_2235026 := by
    simpa [prefixWord, tailWord_2235026, baseEnd_2235026] using wordTrace_append hprefix tailTrace_2235026
  have hstable : (prefixWord ++ tailWord_2235026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235026).length < 2 ^ (prefixWord ++ tailWord_2235026).sum := by decide
  have hdescent : baseEnd_2235026 < baseStart_2235026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235032 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 1, 4, 2]
def baseStart_2235032 : Nat := 118140960795 + 2235032 * 2 ^ 59
def prefixEnd_2235032 : Nat := 4983230072969 + 3 ^ 40 * 2235032 * 2
def baseEnd_2235032 : Nat := 1147645694179804660721281

theorem tailTrace_2235032 : CollatzResearch.WordTrace tailWord_2235032 prefixEnd_2235032 1147645694179804660721281 := by
  unfold tailWord_2235032
  simp only [CollatzResearch.WordTrace]
  refine ⟨40759157019434125960489675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54345542692578834613986233 40759157019434125960489675)
  ·
    refine ⟨61138735529151188940734513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40759157019434125960489675 61138735529151188940734513)
    ·
      refine ⟨45854051646863391705550885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61138735529151188940734513 45854051646863391705550885)
      ·
        refine ⟨8597634683786885944790791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45854051646863391705550885 8597634683786885944790791)
        ·
          refine ⟨12896452025680328917186187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8597634683786885944790791 12896452025680328917186187)
          ·
            refine ⟨19344678038520493375779281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12896452025680328917186187 19344678038520493375779281)
            ·
              refine ⟨14508508528890370031834461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19344678038520493375779281 14508508528890370031834461)
              ·
                refine ⟨5440690698333888761937923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14508508528890370031834461 5440690698333888761937923)
                ·
                  refine ⟨8161036047500833142906885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5440690698333888761937923 8161036047500833142906885)
                  ·
                    refine ⟨1530194258906406214295041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8161036047500833142906885 1530194258906406214295041)
                    ·
                      refine ⟨1147645694179804660721281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530194258906406214295041 1147645694179804660721281)
                      ·
                        rfl

theorem cell23_2235032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_2235032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235032 prefixEnd_2235032 := by exact prefixLift 2235032
  have htrace : WordTrace (prefixWord ++ tailWord_2235032) baseStart_2235032 baseEnd_2235032 := by
    simpa [prefixWord, tailWord_2235032, baseEnd_2235032] using wordTrace_append hprefix tailTrace_2235032
  have hstable : (prefixWord ++ tailWord_2235032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235032).length < 2 ^ (prefixWord ++ tailWord_2235032).sum := by decide
  have hdescent : baseEnd_2235032 < baseStart_2235032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235036 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2235036 : Nat := 118140960795 + 2235036 * 2 ^ 59
def prefixEnd_2235036 : Nat := 4983230072969 + 3 ^ 40 * 2235036 * 2
def baseEnd_2235036 : Nat := 1147647748102422645071263

theorem tailTrace_2235036 : CollatzResearch.WordTrace tailWord_2235036 prefixEnd_2235036 1147647748102422645071263 := by
  unfold tailWord_2235036
  simp only [CollatzResearch.WordTrace]
  refine ⟨40759229965426880302062481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54345639953902507069416641 40759229965426880302062481)
  ·
    refine ⟨30569422474070160226546861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40759229965426880302062481 30569422474070160226546861)
    ·
      refine ⟨11463533427776310084955073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30569422474070160226546861 11463533427776310084955073)
      ·
        refine ⟨8597650070832232563716305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11463533427776310084955073 8597650070832232563716305)
        ·
          refine ⟨6448237553124174422787229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8597650070832232563716305 6448237553124174422787229)
          ·
            refine ⟨2418089082421565408545211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6448237553124174422787229 2418089082421565408545211)
            ·
              refine ⟨3627133623632348112817817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418089082421565408545211 3627133623632348112817817)
              ·
                refine ⟨2720350217724261084613363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3627133623632348112817817 2720350217724261084613363)
                ·
                  refine ⟨4080525326586391626920045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720350217724261084613363 4080525326586391626920045)
                  ·
                    refine ⟨1530196997469896860095017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4080525326586391626920045 1530196997469896860095017)
                    ·
                      refine ⟨1147647748102422645071263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530196997469896860095017 1147647748102422645071263)
                      ·
                        rfl

theorem cell23_2235036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2235036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235036 prefixEnd_2235036 := by exact prefixLift 2235036
  have htrace : WordTrace (prefixWord ++ tailWord_2235036) baseStart_2235036 baseEnd_2235036 := by
    simpa [prefixWord, tailWord_2235036, baseEnd_2235036] using wordTrace_append hprefix tailTrace_2235036
  have hstable : (prefixWord ++ tailWord_2235036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235036).length < 2 ^ (prefixWord ++ tailWord_2235036).sum := by decide
  have hdescent : baseEnd_2235036 < baseStart_2235036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235065 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2235065 : Nat := 118140960795 + 2235065 * 2 ^ 59
def prefixEnd_2235065 : Nat := 4983230072969 + 3 ^ 40 * 2235065 * 2
def baseEnd_2235065 : Nat := 1147662639041403031608629

theorem tailTrace_2235065 : CollatzResearch.WordTrace tailWord_2235065 prefixEnd_2235065 1147662639041403031608629 := by
  unfold tailWord_2235065
  simp only [CollatzResearch.WordTrace]
  refine ⟨81519517647748698556930649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54346345098499132371287099 81519517647748698556930649)
  ·
    refine ⟨61139638235811523917697987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81519517647748698556930649 61139638235811523917697987)
    ·
      refine ⟨91709457353717285876546981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61139638235811523917697987 91709457353717285876546981)
      ·
        refine ⟨17195523253821991101852559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91709457353717285876546981 17195523253821991101852559)
        ·
          refine ⟨25793284880732986652778839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17195523253821991101852559 25793284880732986652778839)
          ·
            refine ⟨38689927321099479979168259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25793284880732986652778839 38689927321099479979168259)
            ·
              refine ⟨58034890981649219968752389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38689927321099479979168259 58034890981649219968752389)
              ·
                refine ⟨10881542059059228744141073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58034890981649219968752389 10881542059059228744141073)
                ·
                  refine ⟨8161156544294421558105805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10881542059059228744141073 8161156544294421558105805)
                  ·
                    refine ⟨3060433704110408084289677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8161156544294421558105805 3060433704110408084289677)
                    ·
                      refine ⟨1147662639041403031608629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060433704110408084289677 1147662639041403031608629)
                      ·
                        rfl

theorem cell23_2235065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2235065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235065 prefixEnd_2235065 := by exact prefixLift 2235065
  have htrace : WordTrace (prefixWord ++ tailWord_2235065) baseStart_2235065 baseEnd_2235065 := by
    simpa [prefixWord, tailWord_2235065, baseEnd_2235065] using wordTrace_append hprefix tailTrace_2235065
  have hstable : (prefixWord ++ tailWord_2235065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235065).length < 2 ^ (prefixWord ++ tailWord_2235065).sum := by decide
  have hdescent : baseEnd_2235065 < baseStart_2235065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235072 : List Nat := [2, 1, 1, 2, 4, 3, 1, 4, 5]
def baseStart_2235072 : Nat := 118140960795 + 2235072 * 2 ^ 59
def prefixEnd_2235072 : Nat := 4983230072969 + 3 ^ 40 * 2235072 * 2
def baseEnd_2235072 : Nat := 127518470378442722691233

theorem tailTrace_2235072 : CollatzResearch.WordTrace tailWord_2235072 prefixEnd_2235072 127518470378442722691233 := by
  unfold tailWord_2235072
  simp only [CollatzResearch.WordTrace]
  refine ⟨40759886479361669376217735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54346515305815559168290313 40759886479361669376217735)
  ·
    refine ⟨61139829719042504064326603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40759886479361669376217735 61139829719042504064326603)
    ·
      refine ⟨91709744578563756096489905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61139829719042504064326603 91709744578563756096489905)
      ·
        refine ⟨68782308433922817072367429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91709744578563756096489905 68782308433922817072367429)
        ·
          refine ⟨12896682831360528201068893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68782308433922817072367429 12896682831360528201068893)
          ·
            refine ⟨4836256061760198075400835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12896682831360528201068893 4836256061760198075400835)
            ·
              refine ⟨7254384092640297113101253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4836256061760198075400835 7254384092640297113101253)
              ·
                refine ⟨1360197017370055708706485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7254384092640297113101253 1360197017370055708706485)
                ·
                  refine ⟨127518470378442722691233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1360197017370055708706485 127518470378442722691233)
                  ·
                    rfl

theorem cell23_2235072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 5].length) (baseStart_2235072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235072 prefixEnd_2235072 := by exact prefixLift 2235072
  have htrace : WordTrace (prefixWord ++ tailWord_2235072) baseStart_2235072 baseEnd_2235072 := by
    simpa [prefixWord, tailWord_2235072, baseEnd_2235072] using wordTrace_append hprefix tailTrace_2235072
  have hstable : (prefixWord ++ tailWord_2235072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235072).length < 2 ^ (prefixWord ++ tailWord_2235072).sum := by decide
  have hdescent : baseEnd_2235072 < baseStart_2235072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235082 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_2235082 : Nat := 118140960795 + 2235082 * 2 ^ 59
def prefixEnd_2235082 : Nat := 4983230072969 + 3 ^ 40 * 2235082 * 2
def baseEnd_2235082 : Nat := 1147671368212529465096051

theorem tailTrace_2235082 : CollatzResearch.WordTrace tailWord_2235082 prefixEnd_2235082 1147671368212529465096051 := by
  unfold tailWord_2235082
  simp only [CollatzResearch.WordTrace]
  refine ⟨20380034422171777615074875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54346758459124740306866333 20380034422171777615074875)
  ·
    refine ⟨30570051633257666422612313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20380034422171777615074875 30570051633257666422612313)
    ·
      refine ⟨22927538724943249816959235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30570051633257666422612313 22927538724943249816959235)
      ·
        refine ⟨34391308087414874725438853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22927538724943249816959235 34391308087414874725438853)
        ·
          refine ⟨6448370266390289011019785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34391308087414874725438853 6448370266390289011019785)
          ·
            refine ⟨4836277699792716758264839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6448370266390289011019785 4836277699792716758264839)
            ·
              refine ⟨7254416549689075137397259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4836277699792716758264839 7254416549689075137397259)
              ·
                refine ⟨10881624824533612706095889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7254416549689075137397259 10881624824533612706095889)
                ·
                  refine ⟨8161218618400209529571917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10881624824533612706095889 8161218618400209529571917)
                  ·
                    refine ⟨3060456981900078573589469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8161218618400209529571917 3060456981900078573589469)
                    ·
                      refine ⟨1147671368212529465096051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060456981900078573589469 1147671368212529465096051)
                      ·
                        rfl

theorem cell23_2235082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_2235082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235082 prefixEnd_2235082 := by exact prefixLift 2235082
  have htrace : WordTrace (prefixWord ++ tailWord_2235082) baseStart_2235082 baseEnd_2235082 := by
    simpa [prefixWord, tailWord_2235082, baseEnd_2235082] using wordTrace_append hprefix tailTrace_2235082
  have hstable : (prefixWord ++ tailWord_2235082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235082).length < 2 ^ (prefixWord ++ tailWord_2235082).sum := by decide
  have hdescent : baseEnd_2235082 < baseStart_2235082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235115 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 7, 4]
def baseStart_2235115 : Nat := 118140960795 + 2235115 * 2 ^ 59
def prefixEnd_2235115 : Nat := 4983230072969 + 3 ^ 40 * 2235115 * 2
def baseEnd_2235115 : Nat := 382562771024709278661133

theorem tailTrace_2235115 : CollatzResearch.WordTrace tailWord_2235115 prefixEnd_2235115 382562771024709278661133 := by
  unfold tailWord_2235115
  simp only [CollatzResearch.WordTrace]
  refine ⟨81521341297567557096250799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54347560865045038064167199 81521341297567557096250799)
  ·
    refine ⟨122282011946351335644376199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81521341297567557096250799 122282011946351335644376199)
    ·
      refine ⟨183423017919527003466564299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122282011946351335644376199 183423017919527003466564299)
      ·
        refine ⟨275134526879290505199846449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183423017919527003466564299 275134526879290505199846449)
        ·
          refine ⟨206350895159467878899884837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275134526879290505199846449 206350895159467878899884837)
          ·
            refine ⟨38690792842400227293728407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206350895159467878899884837 38690792842400227293728407)
            ·
              refine ⟨58036189263600340940592611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38690792842400227293728407 58036189263600340940592611)
              ·
                refine ⟨87054283895400511410888917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58036189263600340940592611 87054283895400511410888917)
                ·
                  refine ⟨2040334778798449486192709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 87054283895400511410888917 2040334778798449486192709)
                  ·
                    refine ⟨382562771024709278661133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040334778798449486192709 382562771024709278661133)
                    ·
                      rfl

theorem cell23_2235115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 4].length) (baseStart_2235115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235115 prefixEnd_2235115 := by exact prefixLift 2235115
  have htrace : WordTrace (prefixWord ++ tailWord_2235115) baseStart_2235115 baseEnd_2235115 := by
    simpa [prefixWord, tailWord_2235115, baseEnd_2235115] using wordTrace_append hprefix tailTrace_2235115
  have hstable : (prefixWord ++ tailWord_2235115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235115).length < 2 ^ (prefixWord ++ tailWord_2235115).sum := by decide
  have hdescent : baseEnd_2235115 < baseStart_2235115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235132 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_2235132 : Nat := 118140960795 + 2235132 * 2 ^ 59
def prefixEnd_2235132 : Nat := 4983230072969 + 3 ^ 40 * 2235132 * 2
def baseEnd_2235132 : Nat := 382565680748418089823607

theorem tailTrace_2235132 : CollatzResearch.WordTrace tailWord_2235132 prefixEnd_2235132 382565680748418089823607 := by
  unfold tailWord_2235132
  simp only [CollatzResearch.WordTrace]
  refine ⟨40760980669252984499809825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54347974225670645999746433 40760980669252984499809825)
  ·
    refine ⟨30570735501939738374857369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40760980669252984499809825 30570735501939738374857369)
    ·
      refine ⟨22928051626454803781143027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30570735501939738374857369 22928051626454803781143027)
      ·
        refine ⟨34392077439682205671714541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22928051626454803781143027 34392077439682205671714541)
        ·
          refine ⟨12897029039880827126892953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34392077439682205671714541 12897029039880827126892953)
          ·
            refine ⟨9672771779910620345169715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12897029039880827126892953 9672771779910620345169715)
            ·
              refine ⟨14509157669865930517754573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9672771779910620345169715 14509157669865930517754573)
              ·
                refine ⟨5440934126199723944157965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14509157669865930517754573 5440934126199723944157965)
                ·
                  refine ⟨2040350297324896479059237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5440934126199723944157965 2040350297324896479059237)
                  ·
                    refine ⟨382565680748418089823607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040350297324896479059237 382565680748418089823607)
                    ·
                      rfl

theorem cell23_2235132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_2235132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235132 prefixEnd_2235132 := by exact prefixLift 2235132
  have htrace : WordTrace (prefixWord ++ tailWord_2235132) baseStart_2235132 baseEnd_2235132 := by
    simpa [prefixWord, tailWord_2235132, baseEnd_2235132] using wordTrace_append hprefix tailTrace_2235132
  have hstable : (prefixWord ++ tailWord_2235132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235132).length < 2 ^ (prefixWord ++ tailWord_2235132).sum := by decide
  have hdescent : baseEnd_2235132 < baseStart_2235132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235145 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 6]
def baseStart_2235145 : Nat := 118140960795 + 2235145 * 2 ^ 59
def prefixEnd_2235145 : Nat := 4983230072969 + 3 ^ 40 * 2235145 * 2
def baseEnd_2235145 : Nat := 127522635277084746512029

theorem tailTrace_2235145 : CollatzResearch.WordTrace tailWord_2235145 prefixEnd_2235145 127522635277084746512029 := by
  unfold tailWord_2235145
  simp only [CollatzResearch.WordTrace]
  refine ⟨81522435487458872219842889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54348290324972581479895259 81522435487458872219842889)
  ·
    refine ⟨61141826615594154164882167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81522435487458872219842889 61141826615594154164882167)
    ·
      refine ⟨91712739923391231247323251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61141826615594154164882167 91712739923391231247323251)
      ·
        refine ⟨137569109885086846870984877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91712739923391231247323251 137569109885086846870984877)
        ·
          refine ⟨51588416206907567576619329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137569109885086846870984877 51588416206907567576619329)
          ·
            refine ⟨38691312155180675682464497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51588416206907567576619329 38691312155180675682464497)
            ·
              refine ⟨29018484116385506761848373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38691312155180675682464497 29018484116385506761848373)
              ·
                refine ⟨2720482885911141258923285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29018484116385506761848373 2720482885911141258923285)
                ·
                  refine ⟨127522635277084746512029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2720482885911141258923285 127522635277084746512029)
                  ·
                    rfl

theorem cell23_2235145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 6].length) (baseStart_2235145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235145 prefixEnd_2235145 := by exact prefixLift 2235145
  have htrace : WordTrace (prefixWord ++ tailWord_2235145) baseStart_2235145 baseEnd_2235145 := by
    simpa [prefixWord, tailWord_2235145, baseEnd_2235145] using wordTrace_append hprefix tailTrace_2235145
  have hstable : (prefixWord ++ tailWord_2235145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235145).length < 2 ^ (prefixWord ++ tailWord_2235145).sum := by decide
  have hdescent : baseEnd_2235145 < baseStart_2235145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235155 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 3]
def baseStart_2235155 : Nat := 118140960795 + 2235155 * 2 ^ 59
def prefixEnd_2235155 : Nat := 4983230072969 + 3 ^ 40 * 2235155 * 2
def baseEnd_2235155 : Nat := 1147708852300307679483215

theorem tailTrace_2235155 : CollatzResearch.WordTrace tailWord_2235155 prefixEnd_2235155 1147708852300307679483215 := by
  unfold tailWord_2235155
  simp only [CollatzResearch.WordTrace]
  refine ⟨81522800217422643927706919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54348533478281762618471279 81522800217422643927706919)
  ·
    refine ⟨122284200326133965891560379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81522800217422643927706919 122284200326133965891560379)
    ·
      refine ⟨183426300489200948837340569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122284200326133965891560379 183426300489200948837340569)
      ·
        refine ⟨137569725366900711628005427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183426300489200948837340569 137569725366900711628005427)
        ·
          refine ⟨206354588050351067442008141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137569725366900711628005427 206354588050351067442008141)
          ·
            refine ⟨77382970518881650290753053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206354588050351067442008141 77382970518881650290753053)
            ·
              refine ⟨29018613944580618859032395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77382970518881650290753053 29018613944580618859032395)
              ·
                refine ⟨43527920916870928288548593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29018613944580618859032395 43527920916870928288548593)
                ·
                  refine ⟨32645940687653196216411445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43527920916870928288548593 32645940687653196216411445)
                  ·
                    refine ⟨3060556939467487145288573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32645940687653196216411445 3060556939467487145288573)
                    ·
                      refine ⟨1147708852300307679483215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060556939467487145288573 1147708852300307679483215)
                      ·
                        rfl

theorem cell23_2235155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_2235155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235155 prefixEnd_2235155 := by exact prefixLift 2235155
  have htrace : WordTrace (prefixWord ++ tailWord_2235155) baseStart_2235155 baseEnd_2235155 := by
    simpa [prefixWord, tailWord_2235155, baseEnd_2235155] using wordTrace_append hprefix tailTrace_2235155
  have hstable : (prefixWord ++ tailWord_2235155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235155).length < 2 ^ (prefixWord ++ tailWord_2235155).sum := by decide
  have hdescent : baseEnd_2235155 < baseStart_2235155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235209 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 1, 5]
def baseStart_2235209 : Nat := 118140960795 + 2235209 * 2 ^ 59
def prefixEnd_2235209 : Nat := 4983230072969 + 3 ^ 40 * 2235209 * 2
def baseEnd_2235209 : Nat := 382578860085216822735989

theorem tailTrace_2235209 : CollatzResearch.WordTrace tailWord_2235209 prefixEnd_2235209 382578860085216822735989 := by
  unfold tailWord_2235209
  simp only [CollatzResearch.WordTrace]
  refine ⟨81524769759227011150172681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54349846506151340766781787 81524769759227011150172681)
  ·
    refine ⟨61143577319420258362629511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81524769759227011150172681 61143577319420258362629511)
    ·
      refine ⟨91715365979130387543944267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61143577319420258362629511 91715365979130387543944267)
      ·
        refine ⟨137573048968695581315916401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91715365979130387543944267 137573048968695581315916401)
        ·
          refine ⟨103179786726521685986937301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137573048968695581315916401 103179786726521685986937301)
          ·
            refine ⟨2418276251402852015318843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103179786726521685986937301 2418276251402852015318843)
            ·
              refine ⟨3627414377104278022978265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418276251402852015318843 3627414377104278022978265)
              ·
                refine ⟨2720560782828208517233699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3627414377104278022978265 2720560782828208517233699)
                ·
                  refine ⟨4080841174242312775850549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720560782828208517233699 4080841174242312775850549)
                  ·
                    refine ⟨382578860085216822735989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4080841174242312775850549 382578860085216822735989)
                    ·
                      rfl

theorem cell23_2235209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_2235209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235209 prefixEnd_2235209 := by exact prefixLift 2235209
  have htrace : WordTrace (prefixWord ++ tailWord_2235209) baseStart_2235209 baseEnd_2235209 := by
    simpa [prefixWord, tailWord_2235209, baseEnd_2235209] using wordTrace_append hprefix tailTrace_2235209
  have hstable : (prefixWord ++ tailWord_2235209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235209).length < 2 ^ (prefixWord ++ tailWord_2235209).sum := by decide
  have hdescent : baseEnd_2235209 < baseStart_2235209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235235 : List Nat := [1, 1, 1, 5, 3, 12]
def baseStart_2235235 : Nat := 118140960795 + 2235235 * 2 ^ 59
def prefixEnd_2235235 : Nat := 4983230072969 + 3 ^ 40 * 2235235 * 2
def baseEnd_2235235 : Nat := 4723250743838137310629

theorem tailTrace_2235235 : CollatzResearch.WordTrace tailWord_2235235 prefixEnd_2235235 4723250743838137310629 := by
  unfold tailWord_2235235
  simp only [CollatzResearch.WordTrace]
  refine ⟨81525718057132817590619159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54350478704755211727079439 81525718057132817590619159)
  ·
    refine ⟨122288577085699226385928739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81525718057132817590619159 122288577085699226385928739)
    ·
      refine ⟨183432865628548839578893109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122288577085699226385928739 183432865628548839578893109)
      ·
        refine ⟨17196831152676453710521229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183432865628548839578893109 17196831152676453710521229)
        ·
          refine ⟨6448811682253670141445461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17196831152676453710521229 6448811682253670141445461)
          ·
            refine ⟨4723250743838137310629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6448811682253670141445461 4723250743838137310629)
            ·
              rfl

theorem cell23_2235235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 12].length) (baseStart_2235235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235235 prefixEnd_2235235 := by exact prefixLift 2235235
  have htrace : WordTrace (prefixWord ++ tailWord_2235235) baseStart_2235235 baseEnd_2235235 := by
    simpa [prefixWord, tailWord_2235235, baseEnd_2235235] using wordTrace_append hprefix tailTrace_2235235
  have hstable : (prefixWord ++ tailWord_2235235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235235).length < 2 ^ (prefixWord ++ tailWord_2235235).sum := by decide
  have hdescent : baseEnd_2235235 < baseStart_2235235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235239 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 2, 4]
def baseStart_2235239 : Nat := 118140960795 + 2235239 * 2 ^ 59
def prefixEnd_2235239 : Nat := 4983230072969 + 3 ^ 40 * 2235239 * 2
def baseEnd_2235239 : Nat := 382583994891761783610943

theorem tailTrace_2235239 : CollatzResearch.WordTrace tailWord_2235239 prefixEnd_2235239 382583994891761783610943 := by
  unfold tailWord_2235239
  simp only [CollatzResearch.WordTrace]
  refine ⟨81525863949118326273764771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54350575966078884182509847 81525863949118326273764771)
  ·
    refine ⟨122288795923677489410647157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81525863949118326273764771 122288795923677489410647157)
    ·
      refine ⟨11464574617844764632248171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122288795923677489410647157 11464574617844764632248171)
      ·
        refine ⟨17196861926767146948372257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11464574617844764632248171 17196861926767146948372257)
        ·
          refine ⟨12897646445075360211279193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17196861926767146948372257 12897646445075360211279193)
          ·
            refine ⟨9673234833806520158459395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12897646445075360211279193 9673234833806520158459395)
            ·
              refine ⟨14509852250709780237689093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9673234833806520158459395 14509852250709780237689093)
              ·
                refine ⟨2720597297008083794566705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14509852250709780237689093 2720597297008083794566705)
                ·
                  refine ⟨2040447972756062845925029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720597297008083794566705 2040447972756062845925029)
                  ·
                    refine ⟨382583994891761783610943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040447972756062845925029 382583994891761783610943)
                    ·
                      rfl

theorem cell23_2235239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_2235239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235239 prefixEnd_2235239 := by exact prefixLift 2235239
  have htrace : WordTrace (prefixWord ++ tailWord_2235239) baseStart_2235239 baseEnd_2235239 := by
    simpa [prefixWord, tailWord_2235239, baseEnd_2235239] using wordTrace_append hprefix tailTrace_2235239
  have hstable : (prefixWord ++ tailWord_2235239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235239).length < 2 ^ (prefixWord ++ tailWord_2235239).sum := by decide
  have hdescent : baseEnd_2235239 < baseStart_2235239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235240 : List Nat := [2, 1, 4, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2235240 : Nat := 118140960795 + 2235240 * 2 ^ 59
def prefixEnd_2235240 : Nat := 4983230072969 + 3 ^ 40 * 2235240 * 2
def baseEnd_2235240 : Nat := 1147752498155939846920325

theorem tailTrace_2235240 : CollatzResearch.WordTrace tailWord_2235240 prefixEnd_2235240 1147752498155939846920325 := by
  unfold tailWord_2235240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40762950211057351722275587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54350600281409802296367449 40762950211057351722275587)
  ·
    refine ⟨61144425316586027583413381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40762950211057351722275587 61144425316586027583413381)
    ·
      refine ⟨11464579746859880171890009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61144425316586027583413381 11464579746859880171890009)
      ·
        refine ⟨8598434810144910128917507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11464579746859880171890009 8598434810144910128917507)
        ·
          refine ⟨12897652215217365193376261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8598434810144910128917507 12897652215217365193376261)
          ·
            refine ⟨2418309790353255973758049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12897652215217365193376261 2418309790353255973758049)
            ·
              refine ⟨1813732342764941980318537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2418309790353255973758049 1813732342764941980318537)
              ·
                refine ⟨1360299257073706485238903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813732342764941980318537 1360299257073706485238903)
                ·
                  refine ⟨2040448885610559727858355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360299257073706485238903 2040448885610559727858355)
                  ·
                    refine ⟨3060673328415839591787533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040448885610559727858355 3060673328415839591787533)
                    ·
                      refine ⟨1147752498155939846920325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060673328415839591787533 1147752498155939846920325)
                      ·
                        rfl

theorem cell23_2235240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2235240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235240 prefixEnd_2235240 := by exact prefixLift 2235240
  have htrace : WordTrace (prefixWord ++ tailWord_2235240) baseStart_2235240 baseEnd_2235240 := by
    simpa [prefixWord, tailWord_2235240, baseEnd_2235240] using wordTrace_append hprefix tailTrace_2235240
  have hstable : (prefixWord ++ tailWord_2235240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235240).length < 2 ^ (prefixWord ++ tailWord_2235240).sum := by decide
  have hdescent : baseEnd_2235240 < baseStart_2235240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235255 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_2235255 : Nat := 118140960795 + 2235255 * 2 ^ 59
def prefixEnd_2235255 : Nat := 4983230072969 + 3 ^ 40 * 2235255 * 2
def baseEnd_2235255 : Nat := 1147760200365757288232755

theorem tailTrace_2235255 : CollatzResearch.WordTrace tailWord_2235255 prefixEnd_2235255 1147760200365757288232755 := by
  unfold tailWord_2235255
  simp only [CollatzResearch.WordTrace]
  refine ⟨81526447517060361006347219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54350965011373574004231479 81526447517060361006347219)
  ·
    refine ⟨122289671275590541509520829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81526447517060361006347219 122289671275590541509520829)
    ·
      refine ⟨45858626728346453066070311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122289671275590541509520829 45858626728346453066070311)
      ·
        refine ⟨68787940092519679599105467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45858626728346453066070311 68787940092519679599105467)
        ·
          refine ⟨103181910138779519398658201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68787940092519679599105467 103181910138779519398658201)
          ·
            refine ⟨77386432604084639548993651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103181910138779519398658201 77386432604084639548993651)
            ·
              refine ⟨116079648906126959323490477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77386432604084639548993651 116079648906126959323490477)
              ·
                refine ⟨43529868339797609746308929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116079648906126959323490477 43529868339797609746308929)
                ·
                  refine ⟨32647401254848207309731697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43529868339797609746308929 32647401254848207309731697)
                  ·
                    refine ⟨24485550941136155482298773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32647401254848207309731697 24485550941136155482298773)
                    ·
                      refine ⟨1147760200365757288232755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24485550941136155482298773 1147760200365757288232755)
                      ·
                        rfl

theorem cell23_2235255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_2235255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235255 prefixEnd_2235255 := by exact prefixLift 2235255
  have htrace : WordTrace (prefixWord ++ tailWord_2235255) baseStart_2235255 baseEnd_2235255 := by
    simpa [prefixWord, tailWord_2235255, baseEnd_2235255] using wordTrace_append hprefix tailTrace_2235255
  have hstable : (prefixWord ++ tailWord_2235255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235255).length < 2 ^ (prefixWord ++ tailWord_2235255).sum := by decide
  have hdescent : baseEnd_2235255 < baseStart_2235255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235286 : List Nat := [5, 3, 1, 1, 1, 2, 10]
def baseStart_2235286 : Nat := 118140960795 + 2235286 * 2 ^ 59
def prefixEnd_2235286 : Nat := 4983230072969 + 3 ^ 40 * 2235286 * 2
def baseEnd_2235286 : Nat := 14170075534148724283273

theorem tailTrace_2235286 : CollatzResearch.WordTrace tailWord_2235286 prefixEnd_2235286 14170075534148724283273 := by
  unfold tailWord_2235286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095473636246753331295357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54351718786632035533817141 5095473636246753331295357)
  ·
    refine ⟨1910802613592532499235759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5095473636246753331295357 1910802613592532499235759)
    ·
      refine ⟨2866203920388798748853639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1910802613592532499235759 2866203920388798748853639)
      ·
        refine ⟨4299305880583198123280459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2866203920388798748853639 4299305880583198123280459)
        ·
          refine ⟨6448958820874797184920689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299305880583198123280459 6448958820874797184920689)
          ·
            refine ⟨4836719115656097888690517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6448958820874797184920689 4836719115656097888690517)
            ·
              refine ⟨14170075534148724283273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4836719115656097888690517 14170075534148724283273)
              ·
                rfl

theorem cell23_2235286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 10].length) (baseStart_2235286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235286 prefixEnd_2235286 := by exact prefixLift 2235286
  have htrace : WordTrace (prefixWord ++ tailWord_2235286) baseStart_2235286 baseEnd_2235286 := by
    simpa [prefixWord, tailWord_2235286, baseEnd_2235286] using wordTrace_append hprefix tailTrace_2235286
  have hstable : (prefixWord ++ tailWord_2235286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235286).length < 2 ^ (prefixWord ++ tailWord_2235286).sum := by decide
  have hdescent : baseEnd_2235286 < baseStart_2235286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235296 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2235296 : Nat := 118140960795 + 2235296 * 2 ^ 59
def prefixEnd_2235296 : Nat := 4983230072969 + 3 ^ 40 * 2235296 * 2
def baseEnd_2235296 : Nat := 1147781253072591627820067

theorem tailTrace_2235296 : CollatzResearch.WordTrace tailWord_2235296 prefixEnd_2235296 1147781253072591627820067 := by
  unfold tailWord_2235296
  simp only [CollatzResearch.WordTrace]
  refine ⟨40763971454955912504294871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54351961939941216672393161 40763971454955912504294871)
  ·
    refine ⟨61145957182433868756442307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40763971454955912504294871 61145957182433868756442307)
    ·
      refine ⟨91718935773650803134663461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61145957182433868756442307 91718935773650803134663461)
      ·
        refine ⟨17197300457559525587749399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91718935773650803134663461 17197300457559525587749399)
        ·
          refine ⟨25795950686339288381624099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17197300457559525587749399 25795950686339288381624099)
          ·
            refine ⟨38693926029508932572436149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25795950686339288381624099 38693926029508932572436149)
            ·
              refine ⟨3627555565266462428665889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38693926029508932572436149 3627555565266462428665889)
              ·
                refine ⟨2720666673949846821499417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3627555565266462428665889 2720666673949846821499417)
                ·
                  refine ⟨2040500005462385116124563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720666673949846821499417 2040500005462385116124563)
                  ·
                    refine ⟨3060750008193577674186845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040500005462385116124563 3060750008193577674186845)
                    ·
                      refine ⟨1147781253072591627820067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060750008193577674186845 1147781253072591627820067)
                      ·
                        rfl

theorem cell23_2235296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2235296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235296 prefixEnd_2235296 := by exact prefixLift 2235296
  have htrace : WordTrace (prefixWord ++ tailWord_2235296) baseStart_2235296 baseEnd_2235296 := by
    simpa [prefixWord, tailWord_2235296, baseEnd_2235296] using wordTrace_append hprefix tailTrace_2235296
  have hstable : (prefixWord ++ tailWord_2235296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235296).length < 2 ^ (prefixWord ++ tailWord_2235296).sum := by decide
  have hdescent : baseEnd_2235296 < baseStart_2235296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235313 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 1, 3, 3]
def baseStart_2235313 : Nat := 118140960795 + 2235313 * 2 ^ 59
def prefixEnd_2235313 : Nat := 4983230072969 + 3 ^ 40 * 2235313 * 2
def baseEnd_2235313 : Nat := 1147789982243718061307489

theorem tailTrace_2235313 : CollatzResearch.WordTrace tailWord_2235313 prefixEnd_2235313 1147789982243718061307489 := by
  unfold tailWord_2235313
  simp only [CollatzResearch.WordTrace]
  refine ⟨81528562950850236911958593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54352375300566824607972395 81528562950850236911958593)
  ·
    refine ⟨61146422213137677683968945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81528562950850236911958593 61146422213137677683968945)
    ·
      refine ⟨45859816659853258262976709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61146422213137677683968945 45859816659853258262976709)
      ·
        refine ⟨8598715623722485924308133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45859816659853258262976709 8598715623722485924308133)
        ·
          refine ⟨1612259179447966110807775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8598715623722485924308133 1612259179447966110807775)
          ·
            refine ⟨2418388769171949166211663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612259179447966110807775 2418388769171949166211663)
            ·
              refine ⟨3627583153757923749317495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418388769171949166211663 3627583153757923749317495)
              ·
                refine ⟨5441374730636885623976243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3627583153757923749317495 5441374730636885623976243)
                ·
                  refine ⟨8162062095955328435964365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5441374730636885623976243 8162062095955328435964365)
                  ·
                    refine ⟨3060773285983248163486637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8162062095955328435964365 3060773285983248163486637)
                    ·
                      refine ⟨1147789982243718061307489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060773285983248163486637 1147789982243718061307489)
                      ·
                        rfl

theorem cell23_2235313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_2235313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235313 prefixEnd_2235313 := by exact prefixLift 2235313
  have htrace : WordTrace (prefixWord ++ tailWord_2235313) baseStart_2235313 baseEnd_2235313 := by
    simpa [prefixWord, tailWord_2235313, baseEnd_2235313] using wordTrace_append hprefix tailTrace_2235313
  have hstable : (prefixWord ++ tailWord_2235313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235313).length < 2 ^ (prefixWord ++ tailWord_2235313).sum := by decide
  have hdescent : baseEnd_2235313 < baseStart_2235313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235322 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_2235322 : Nat := 118140960795 + 2235322 * 2 ^ 59
def prefixEnd_2235322 : Nat := 4983230072969 + 3 ^ 40 * 2235322 * 2
def baseEnd_2235322 : Nat := 1147794603569608526094947

theorem tailTrace_2235322 : CollatzResearch.WordTrace tailWord_2235322 prefixEnd_2235322 1147794603569608526094947 := by
  unfold tailWord_2235322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20382222801954407862259055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54352594138545087632690813 20382222801954407862259055)
  ·
    refine ⟨30573334202931611793388583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20382222801954407862259055 30573334202931611793388583)
    ·
      refine ⟨45860001304397417690082875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30573334202931611793388583 45860001304397417690082875)
      ·
        refine ⟨68790001956596126535124313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45860001304397417690082875 68790001956596126535124313)
        ·
          refine ⟨51592501467447094901343235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68790001956596126535124313 51592501467447094901343235)
          ·
            refine ⟨77388752201170642352014853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51592501467447094901343235 77388752201170642352014853)
            ·
              refine ⟨14510391037719495441002785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77388752201170642352014853 14510391037719495441002785)
              ·
                refine ⟨10882793278289621580752089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14510391037719495441002785 10882793278289621580752089)
                ·
                  refine ⟨8162094958717216185564067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10882793278289621580752089 8162094958717216185564067)
                  ·
                    refine ⟨12243142438075824278346101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8162094958717216185564067 12243142438075824278346101)
                    ·
                      refine ⟨1147794603569608526094947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12243142438075824278346101 1147794603569608526094947)
                      ·
                        rfl

theorem cell23_2235322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_2235322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235322 prefixEnd_2235322 := by exact prefixLift 2235322
  have htrace : WordTrace (prefixWord ++ tailWord_2235322) baseStart_2235322 baseEnd_2235322 := by
    simpa [prefixWord, tailWord_2235322, baseEnd_2235322] using wordTrace_append hprefix tailTrace_2235322
  have hstable : (prefixWord ++ tailWord_2235322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235322).length < 2 ^ (prefixWord ++ tailWord_2235322).sum := by decide
  have hdescent : baseEnd_2235322 < baseStart_2235322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235370 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_2235370 : Nat := 118140960795 + 2235370 * 2 ^ 59
def prefixEnd_2235370 : Nat := 4983230072969 + 3 ^ 40 * 2235370 * 2
def baseEnd_2235370 : Nat := 1147819250641024338294727

theorem tailTrace_2235370 : CollatzResearch.WordTrace tailWord_2235370 prefixEnd_2235370 1147819250641024338294727 := by
  unfold tailWord_2235370
  simp only [CollatzResearch.WordTrace]
  refine ⟨20382660477910933911695891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54353761274429157097855709 20382660477910933911695891)
  ·
    refine ⟨30573990716866400867543837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20382660477910933911695891 30573990716866400867543837)
    ·
      refine ⟨11465246518824900325328939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30573990716866400867543837 11465246518824900325328939)
      ·
        refine ⟨17197869778237350487993409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11465246518824900325328939 17197869778237350487993409)
        ·
          refine ⟨12898402333678012865995057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17197869778237350487993409 12898402333678012865995057)
          ·
            refine ⟨9673801750258509649496293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12898402333678012865995057 9673801750258509649496293)
            ·
              refine ⟨1813837828173470559280555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9673801750258509649496293 1813837828173470559280555)
              ·
                refine ⟨2720756742260205838920833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813837828173470559280555 2720756742260205838920833)
                ·
                  refine ⟨2040567556695154379190625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720756742260205838920833 2040567556695154379190625)
                  ·
                    refine ⟨1530425667521365784392969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2040567556695154379190625 1530425667521365784392969)
                    ·
                      refine ⟨1147819250641024338294727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530425667521365784392969 1147819250641024338294727)
                      ·
                        rfl

theorem cell23_2235370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_2235370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235370 prefixEnd_2235370 := by exact prefixLift 2235370
  have htrace : WordTrace (prefixWord ++ tailWord_2235370) baseStart_2235370 baseEnd_2235370 := by
    simpa [prefixWord, tailWord_2235370, baseEnd_2235370] using wordTrace_append hprefix tailTrace_2235370
  have hstable : (prefixWord ++ tailWord_2235370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235370).length < 2 ^ (prefixWord ++ tailWord_2235370).sum := by decide
  have hdescent : baseEnd_2235370 < baseStart_2235370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235392 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_2235392 : Nat := 118140960795 + 2235392 * 2 ^ 59
def prefixEnd_2235392 : Nat := 4983230072969 + 3 ^ 40 * 2235392 * 2
def baseEnd_2235392 : Nat := 1147830547215423252219625

theorem tailTrace_2235392 : CollatzResearch.WordTrace tailWord_2235392 prefixEnd_2235392 1147830547215423252219625 := by
  unfold tailWord_2235392
  simp only [CollatzResearch.WordTrace]
  refine ⟨40765722158782016702042215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54354296211709355602722953 40765722158782016702042215)
  ·
    refine ⟨61148583238173025053063323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40765722158782016702042215 61148583238173025053063323)
    ·
      refine ⟨91722874857259537579594985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61148583238173025053063323 91722874857259537579594985)
      ·
        refine ⟨68792156142944653184696239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91722874857259537579594985 68792156142944653184696239)
        ·
          refine ⟨103188234214416979777044359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68792156142944653184696239 103188234214416979777044359)
          ·
            refine ⟨154782351321625469665566539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103188234214416979777044359 154782351321625469665566539)
            ·
              refine ⟨232173526982438204498349809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154782351321625469665566539 232173526982438204498349809)
              ·
                refine ⟨174130145236828653373762357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232173526982438204498349809 174130145236828653373762357)
                ·
                  refine ⟨16324701115952686253790221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174130145236828653373762357 16324701115952686253790221)
                  ·
                    refine ⟨6121762918482257345171333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16324701115952686253790221 6121762918482257345171333)
                    ·
                      refine ⟨1147830547215423252219625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6121762918482257345171333 1147830547215423252219625)
                      ·
                        rfl

theorem cell23_2235392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_2235392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235392 prefixEnd_2235392 := by exact prefixLift 2235392
  have htrace : WordTrace (prefixWord ++ tailWord_2235392) baseStart_2235392 baseEnd_2235392 := by
    simpa [prefixWord, tailWord_2235392, baseEnd_2235392] using wordTrace_append hprefix tailTrace_2235392
  have hstable : (prefixWord ++ tailWord_2235392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235392).length < 2 ^ (prefixWord ++ tailWord_2235392).sum := by decide
  have hdescent : baseEnd_2235392 < baseStart_2235392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235409 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 3, 6, 2]
def baseStart_2235409 : Nat := 118140960795 + 2235409 * 2 ^ 59
def prefixEnd_2235409 : Nat := 4983230072969 + 3 ^ 40 * 2235409 * 2
def baseEnd_2235409 : Nat := 1147839276386549685707047

theorem tailTrace_2235409 : CollatzResearch.WordTrace tailWord_2235409 prefixEnd_2235409 1147839276386549685707047 := by
  unfold tailWord_2235409
  simp only [CollatzResearch.WordTrace]
  refine ⟨81532064358502445307453281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54354709572334963538302187 81532064358502445307453281)
  ·
    refine ⟨61149048268876833980589961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81532064358502445307453281 61149048268876833980589961)
    ·
      refine ⟨45861786201657625485442471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61149048268876833980589961 45861786201657625485442471)
      ·
        refine ⟨68792679302486438228163707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45861786201657625485442471 68792679302486438228163707)
        ·
          refine ⟨103189018953729657342245561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68792679302486438228163707 103189018953729657342245561)
          ·
            refine ⟨77391764215297243006684171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103189018953729657342245561 77391764215297243006684171)
            ·
              refine ⟨116087646322945864510026257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77391764215297243006684171 116087646322945864510026257)
              ·
                refine ⟨87065734742209398382519693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116087646322945864510026257 87065734742209398382519693)
                ·
                  refine ⟨32649650528328524393444885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87065734742209398382519693 32649650528328524393444885)
                  ·
                    refine ⟨1530452368515399580942729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32649650528328524393444885 1530452368515399580942729)
                    ·
                      refine ⟨1147839276386549685707047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530452368515399580942729 1147839276386549685707047)
                      ·
                        rfl

theorem cell23_2235409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_2235409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235409 prefixEnd_2235409 := by exact prefixLift 2235409
  have htrace : WordTrace (prefixWord ++ tailWord_2235409) baseStart_2235409 baseEnd_2235409 := by
    simpa [prefixWord, tailWord_2235409, baseEnd_2235409] using wordTrace_append hprefix tailTrace_2235409
  have hstable : (prefixWord ++ tailWord_2235409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235409).length < 2 ^ (prefixWord ++ tailWord_2235409).sum := by decide
  have hdescent : baseEnd_2235409 < baseStart_2235409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235426 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_2235426 : Nat := 118140960795 + 2235426 * 2 ^ 59
def prefixEnd_2235426 : Nat := 4983230072969 + 3 ^ 40 * 2235426 * 2
def baseEnd_2235426 : Nat := 1147848005557676119194469

theorem tailTrace_2235426 : CollatzResearch.WordTrace tailWord_2235426 prefixEnd_2235426 1147848005557676119194469 := by
  unfold tailWord_2235426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20383171099860214302705533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54355122932960571473881421 20383171099860214302705533)
  ·
    refine ⟨7643689162447580363514575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20383171099860214302705533 7643689162447580363514575)
    ·
      refine ⟨11465533743671370545271863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7643689162447580363514575 11465533743671370545271863)
      ·
        refine ⟨17198300615507055817907795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11465533743671370545271863 17198300615507055817907795)
        ·
          refine ⟨25797450923260583726861693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17198300615507055817907795 25797450923260583726861693)
          ·
            refine ⟨9674044096222718897573135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25797450923260583726861693 9674044096222718897573135)
            ·
              refine ⟨14511066144334078346359703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9674044096222718897573135 14511066144334078346359703)
              ·
                refine ⟨21766599216501117519539555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14511066144334078346359703 21766599216501117519539555)
                ·
                  refine ⟨32649898824751676279309333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21766599216501117519539555 32649898824751676279309333)
                  ·
                    refine ⟨1530464007410234825592625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32649898824751676279309333 1530464007410234825592625)
                    ·
                      refine ⟨1147848005557676119194469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530464007410234825592625 1147848005557676119194469)
                      ·
                        rfl

theorem cell23_2235426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_2235426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235426 prefixEnd_2235426 := by exact prefixLift 2235426
  have htrace : WordTrace (prefixWord ++ tailWord_2235426) baseStart_2235426 baseEnd_2235426 := by
    simpa [prefixWord, tailWord_2235426, baseEnd_2235426] using wordTrace_append hprefix tailTrace_2235426
  have hstable : (prefixWord ++ tailWord_2235426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235426).length < 2 ^ (prefixWord ++ tailWord_2235426).sum := by decide
  have hdescent : baseEnd_2235426 < baseStart_2235426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235429 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_2235429 : Nat := 118140960795 + 2235429 * 2 ^ 59
def prefixEnd_2235429 : Nat := 4983230072969 + 3 ^ 40 * 2235429 * 2
def baseEnd_2235429 : Nat := 1147849545999639607456955

theorem tailTrace_2235429 : CollatzResearch.WordTrace tailWord_2235429 prefixEnd_2235429 1147849545999639607456955 := by
  unfold tailWord_2235429
  simp only [CollatzResearch.WordTrace]
  refine ⟨81532793818429988723181341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54355195878953325815454227 81532793818429988723181341)
  ·
    refine ⟨30574797681911245771193003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81532793818429988723181341 30574797681911245771193003)
    ·
      refine ⟨45862196522866868656789505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30574797681911245771193003 45862196522866868656789505)
      ·
        refine ⟨34396647392150151492592129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45862196522866868656789505 34396647392150151492592129)
        ·
          refine ⟨25797485544112613619444097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34396647392150151492592129 25797485544112613619444097)
          ·
            refine ⟨19348114158084460214583073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25797485544112613619444097 19348114158084460214583073)
            ·
              refine ⟨14511085618563345160937305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19348114158084460214583073 14511085618563345160937305)
              ·
                refine ⟨10883314213922508870702979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14511085618563345160937305 10883314213922508870702979)
                ·
                  refine ⟨16324971320883763306054469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10883314213922508870702979 16324971320883763306054469)
                  ·
                    refine ⟨3060932122665705619885213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16324971320883763306054469 3060932122665705619885213)
                    ·
                      refine ⟨1147849545999639607456955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3060932122665705619885213 1147849545999639607456955)
                      ·
                        rfl

theorem cell23_2235429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_2235429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235429 prefixEnd_2235429 := by exact prefixLift 2235429
  have htrace : WordTrace (prefixWord ++ tailWord_2235429) baseStart_2235429 baseEnd_2235429 := by
    simpa [prefixWord, tailWord_2235429, baseEnd_2235429] using wordTrace_append hprefix tailTrace_2235429
  have hstable : (prefixWord ++ tailWord_2235429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235429).length < 2 ^ (prefixWord ++ tailWord_2235429).sum := by decide
  have hdescent : baseEnd_2235429 < baseStart_2235429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235453 : List Nat := [1, 4, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_2235453 : Nat := 118140960795 + 2235453 * 2 ^ 59
def prefixEnd_2235453 : Nat := 4983230072969 + 3 ^ 40 * 2235453 * 2
def baseEnd_2235453 : Nat := 382620623178449171185615

theorem tailTrace_2235453 : CollatzResearch.WordTrace tailWord_2235453 prefixEnd_2235453 382620623178449171185615 := by
  unfold tailWord_2235453
  simp only [CollatzResearch.WordTrace]
  refine ⟨81533669170343040822055013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54355779446895360548036675 81533669170343040822055013)
  ·
    refine ⟨15287562969439320154135315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81533669170343040822055013 15287562969439320154135315)
    ·
      refine ⟨22931344454158980231202973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15287562969439320154135315 22931344454158980231202973)
      ·
        refine ⟨8599254170309617586701115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22931344454158980231202973 8599254170309617586701115)
        ·
          refine ⟨12898881255464426380051673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8599254170309617586701115 12898881255464426380051673)
          ·
            refine ⟨9674160941598319785038755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12898881255464426380051673 9674160941598319785038755)
            ·
              refine ⟨14511241412397479677558133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9674160941598319785038755 14511241412397479677558133)
              ·
                refine ⟨1360428882412263719771075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14511241412397479677558133 1360428882412263719771075)
                ·
                  refine ⟨2040643323618395579656613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360428882412263719771075 2040643323618395579656613)
                  ·
                    refine ⟨382620623178449171185615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040643323618395579656613 382620623178449171185615)
                    ·
                      rfl

theorem cell23_2235453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_2235453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235453 prefixEnd_2235453 := by exact prefixLift 2235453
  have htrace : WordTrace (prefixWord ++ tailWord_2235453) baseStart_2235453 baseEnd_2235453 := by
    simpa [prefixWord, tailWord_2235453, baseEnd_2235453] using wordTrace_append hprefix tailTrace_2235453
  have hstable : (prefixWord ++ tailWord_2235453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235453).length < 2 ^ (prefixWord ++ tailWord_2235453).sum := by decide
  have hdescent : baseEnd_2235453 < baseStart_2235453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235516 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_2235516 : Nat := 118140960795 + 2235516 * 2 ^ 59
def prefixEnd_2235516 : Nat := 4983230072969 + 3 ^ 40 * 2235516 * 2
def baseEnd_2235516 : Nat := 1147894218816580767069055

theorem tailTrace_2235516 : CollatzResearch.WordTrace tailWord_2235516 prefixEnd_2235516 1147894218816580767069055 := by
  unfold tailWord_2235516
  simp only [CollatzResearch.WordTrace]
  refine ⟨40767983484557401290799201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54357311312743201721065601 40767983484557401290799201)
  ·
    refine ⟨30575987613418050968099401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40767983484557401290799201 30575987613418050968099401)
    ·
      refine ⟨22931990710063538226074551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30575987613418050968099401 22931990710063538226074551)
      ·
        refine ⟨34397986065095307339111827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22931990710063538226074551 34397986065095307339111827)
        ·
          refine ⟨51596979097642961008667741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34397986065095307339111827 51596979097642961008667741)
          ·
            refine ⟨19348867161616110378250403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51596979097642961008667741 19348867161616110378250403)
            ·
              refine ⟨29023300742424165567375605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19348867161616110378250403 29023300742424165567375605)
              ·
                refine ⟨2720934444602265521941463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29023300742424165567375605 2720934444602265521941463)
                ·
                  refine ⟨4081401666903398282912195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720934444602265521941463 4081401666903398282912195)
                  ·
                    refine ⟨6122102500355097424368293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4081401666903398282912195 6122102500355097424368293)
                    ·
                      refine ⟨1147894218816580767069055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6122102500355097424368293 1147894218816580767069055)
                      ·
                        rfl

theorem cell23_2235516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_2235516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235516 prefixEnd_2235516 := by exact prefixLift 2235516
  have htrace : WordTrace (prefixWord ++ tailWord_2235516) baseStart_2235516 baseEnd_2235516 := by
    simpa [prefixWord, tailWord_2235516, baseEnd_2235516] using wordTrace_append hprefix tailTrace_2235516
  have hstable : (prefixWord ++ tailWord_2235516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235516).length < 2 ^ (prefixWord ++ tailWord_2235516).sum := by decide
  have hdescent : baseEnd_2235516 < baseStart_2235516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235529 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_2235529 : Nat := 118140960795 + 2235529 * 2 ^ 59
def prefixEnd_2235529 : Nat := 4983230072969 + 3 ^ 40 * 2235529 * 2
def baseEnd_2235529 : Nat := 1147900894065089216206495

theorem tailTrace_2235529 : CollatzResearch.WordTrace tailWord_2235529 prefixEnd_2235529 1147900894065089216206495 := by
  unfold tailWord_2235529
  simp only [CollatzResearch.WordTrace]
  refine ⟨81536441118067705801821641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54357627412045137201214427 81536441118067705801821641)
  ·
    refine ⟨61152330838550779351366231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81536441118067705801821641 61152330838550779351366231)
    ·
      refine ⟨91728496257826169027049347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61152330838550779351366231 91728496257826169027049347)
      ·
        refine ⟨137592744386739253540574021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91728496257826169027049347 137592744386739253540574021)
        ·
          refine ⟨25798639572513610038857629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137592744386739253540574021 25798639572513610038857629)
          ·
            refine ⟨9674489839692603764571611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25798639572513610038857629 9674489839692603764571611)
            ·
              refine ⟨14511734759538905646857417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9674489839692603764571611 14511734759538905646857417)
              ·
                refine ⟨10883801069654179235143063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14511734759538905646857417 10883801069654179235143063)
                ·
                  refine ⟨16325701604481268852714595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10883801069654179235143063 16325701604481268852714595)
                  ·
                    refine ⟨24488552406721903279071893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16325701604481268852714595 24488552406721903279071893)
                    ·
                      refine ⟨1147900894065089216206495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24488552406721903279071893 1147900894065089216206495)
                      ·
                        rfl

theorem cell23_2235529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_2235529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235529 prefixEnd_2235529 := by exact prefixLift 2235529
  have htrace : WordTrace (prefixWord ++ tailWord_2235529) baseStart_2235529 baseEnd_2235529 := by
    simpa [prefixWord, tailWord_2235529, baseEnd_2235529] using wordTrace_append hprefix tailTrace_2235529
  have hstable : (prefixWord ++ tailWord_2235529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235529).length < 2 ^ (prefixWord ++ tailWord_2235529).sum := by decide
  have hdescent : baseEnd_2235529 < baseStart_2235529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235543 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 2, 4]
def baseStart_2235543 : Nat := 118140960795 + 2235543 * 2 ^ 59
def prefixEnd_2235543 : Nat := 4983230072969 + 3 ^ 40 * 2235543 * 2
def baseEnd_2235543 : Nat := 382636027598084053810477

theorem tailTrace_2235543 : CollatzResearch.WordTrace tailWord_2235543 prefixEnd_2235543 382636027598084053810477 := by
  unfold tailWord_2235543
  simp only [CollatzResearch.WordTrace]
  refine ⟨81536951740016986192831283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54357967826677990795220855 81536951740016986192831283)
  ·
    refine ⟨122305427610025479289246925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81536951740016986192831283 122305427610025479289246925)
    ·
      refine ⟨45864535353759554733467597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122305427610025479289246925 45864535353759554733467597)
      ·
        refine ⟨17199200757659833025050349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45864535353759554733467597 17199200757659833025050349)
        ·
          refine ⟨6449700284122437384393881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17199200757659833025050349 6449700284122437384393881)
          ·
            refine ⟨4837275213091828038295411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6449700284122437384393881 4837275213091828038295411)
            ·
              refine ⟨7255912819637742057443117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837275213091828038295411 7255912819637742057443117)
              ·
                refine ⟨2720967307364153271541169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7255912819637742057443117 2720967307364153271541169)
                ·
                  refine ⟨2040725480523114953655877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720967307364153271541169 2040725480523114953655877)
                  ·
                    refine ⟨382636027598084053810477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040725480523114953655877 382636027598084053810477)
                    ·
                      rfl

theorem cell23_2235543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_2235543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235543 prefixEnd_2235543 := by exact prefixLift 2235543
  have htrace : WordTrace (prefixWord ++ tailWord_2235543) baseStart_2235543 baseEnd_2235543 := by
    simpa [prefixWord, tailWord_2235543, baseEnd_2235543] using wordTrace_append hprefix tailTrace_2235543
  have hstable : (prefixWord ++ tailWord_2235543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235543).length < 2 ^ (prefixWord ++ tailWord_2235543).sum := by decide
  have hdescent : baseEnd_2235543 < baseStart_2235543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235546 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2235546 : Nat := 118140960795 + 2235546 * 2 ^ 59
def prefixEnd_2235546 : Nat := 4983230072969 + 3 ^ 40 * 2235546 * 2
def baseEnd_2235546 : Nat := 1147909623236215649693917

theorem tailTrace_2235546 : CollatzResearch.WordTrace tailWord_2235546 prefixEnd_2235546 1147909623236215649693917 := by
  unfold tailWord_2235546
  simp only [CollatzResearch.WordTrace]
  refine ⟨20384265289751529426297623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54358040772670745136793661 20384265289751529426297623)
  ·
    refine ⟨30576397934627294139446435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20384265289751529426297623 30576397934627294139446435)
    ·
      refine ⟨45864596901940941209169653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30576397934627294139446435 45864596901940941209169653)
      ·
        refine ⟨4299805959556963238359655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45864596901940941209169653 4299805959556963238359655)
        ·
          refine ⟨6449708939335444857539483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299805959556963238359655 6449708939335444857539483)
          ·
            refine ⟨9674563409003167286309225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6449708939335444857539483 9674563409003167286309225)
            ·
              refine ⟨7255922556752375464731919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9674563409003167286309225 7255922556752375464731919)
              ·
                refine ⟨10883883835128563197097879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7255922556752375464731919 10883883835128563197097879)
                ·
                  refine ⟨16325825752692844795646819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10883883835128563197097879 16325825752692844795646819)
                  ·
                    refine ⟨24488738629039267193470229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16325825752692844795646819 24488738629039267193470229)
                    ·
                      refine ⟨1147909623236215649693917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24488738629039267193470229 1147909623236215649693917)
                      ·
                        rfl

theorem cell23_2235546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2235546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235546 prefixEnd_2235546 := by exact prefixLift 2235546
  have htrace : WordTrace (prefixWord ++ tailWord_2235546) baseStart_2235546 baseEnd_2235546 := by
    simpa [prefixWord, tailWord_2235546, baseEnd_2235546] using wordTrace_append hprefix tailTrace_2235546
  have hstable : (prefixWord ++ tailWord_2235546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235546).length < 2 ^ (prefixWord ++ tailWord_2235546).sum := by decide
  have hdescent : baseEnd_2235546 < baseStart_2235546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235550 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2235550 : Nat := 118140960795 + 2235550 * 2 ^ 59
def prefixEnd_2235550 : Nat := 4983230072969 + 3 ^ 40 * 2235550 * 2
def baseEnd_2235550 : Nat := 1147911677158833634043899

theorem tailTrace_2235550 : CollatzResearch.WordTrace tailWord_2235550 prefixEnd_2235550 1147911677158833634043899 := by
  unfold tailWord_2235550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10192150881373953298542013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54358138033994417592224069 10192150881373953298542013)
  ·
    refine ⟨3822056580515232486953255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10192150881373953298542013 3822056580515232486953255)
    ·
      refine ⟨5733084870772848730429883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822056580515232486953255 5733084870772848730429883)
      ·
        refine ⟨8599627306159273095644825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5733084870772848730429883 8599627306159273095644825)
        ·
          refine ⟨6449720479619454821733619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8599627306159273095644825 6449720479619454821733619)
          ·
            refine ⟨9674580719429182232600429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6449720479619454821733619 9674580719429182232600429)
            ·
              refine ⟨3627967769785943337225161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9674580719429182232600429 3627967769785943337225161)
              ·
                refine ⟨2720975827339457502918871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3627967769785943337225161 2720975827339457502918871)
                ·
                  refine ⟨4081463741009186254378307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720975827339457502918871 4081463741009186254378307)
                  ·
                    refine ⟨6122195611513779381567461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4081463741009186254378307 6122195611513779381567461)
                    ·
                      refine ⟨1147911677158833634043899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6122195611513779381567461 1147911677158833634043899)
                      ·
                        rfl

theorem cell23_2235550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2235550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235550 prefixEnd_2235550 := by exact prefixLift 2235550
  have htrace : WordTrace (prefixWord ++ tailWord_2235550) baseStart_2235550 baseEnd_2235550 := by
    simpa [prefixWord, tailWord_2235550, baseEnd_2235550] using wordTrace_append hprefix tailTrace_2235550
  have hstable : (prefixWord ++ tailWord_2235550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235550).length < 2 ^ (prefixWord ++ tailWord_2235550).sum := by decide
  have hdescent : baseEnd_2235550 < baseStart_2235550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235570 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_2235570 : Nat := 118140960795 + 2235570 * 2 ^ 59
def prefixEnd_2235570 : Nat := 4983230072969 + 3 ^ 40 * 2235570 * 2
def baseEnd_2235570 : Nat := 1147921946771923555793807

theorem tailTrace_2235570 : CollatzResearch.WordTrace tailWord_2235570 prefixEnd_2235570 1147921946771923555793807 := by
  unfold tailWord_2235570
  simp only [CollatzResearch.WordTrace]
  refine ⟨20384484127729792451016041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54358624340612779869376109 20384484127729792451016041)
  ·
    refine ⟨15288363095797344338262031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20384484127729792451016041 15288363095797344338262031)
    ·
      refine ⟨22932544643696016507393047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15288363095797344338262031 22932544643696016507393047)
      ·
        refine ⟨34398816965544024761089571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22932544643696016507393047 34398816965544024761089571)
        ·
          refine ⟨51598225448316037141634357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34398816965544024761089571 51598225448316037141634357)
          ·
            refine ⟨4837333635779628482028221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51598225448316037141634357 4837333635779628482028221)
            ·
              refine ⟨1814000113417360680760583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4837333635779628482028221 1814000113417360680760583)
              ·
                refine ⟨2721000170126041021140875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814000113417360680760583 2721000170126041021140875)
                ·
                  refine ⟨4081500255189061531711313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721000170126041021140875 4081500255189061531711313)
                  ·
                    refine ⟨3061125191391796148783485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4081500255189061531711313 3061125191391796148783485)
                    ·
                      refine ⟨1147921946771923555793807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061125191391796148783485 1147921946771923555793807)
                      ·
                        rfl

theorem cell23_2235570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_2235570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235570 prefixEnd_2235570 := by exact prefixLift 2235570
  have htrace : WordTrace (prefixWord ++ tailWord_2235570) baseStart_2235570 baseEnd_2235570 := by
    simpa [prefixWord, tailWord_2235570, baseEnd_2235570] using wordTrace_append hprefix tailTrace_2235570
  have hstable : (prefixWord ++ tailWord_2235570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235570).length < 2 ^ (prefixWord ++ tailWord_2235570).sum := by decide
  have hdescent : baseEnd_2235570 < baseStart_2235570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235583 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 3]
def baseStart_2235583 : Nat := 118140960795 + 2235583 * 2 ^ 59
def prefixEnd_2235583 : Nat := 4983230072969 + 3 ^ 40 * 2235583 * 2
def baseEnd_2235583 : Nat := 1147928622020432004931247

theorem tailTrace_2235583 : CollatzResearch.WordTrace tailWord_2235583 prefixEnd_2235583 1147928622020432004931247 := by
  unfold tailWord_2235583
  simp only [CollatzResearch.WordTrace]
  refine ⟨81538410659872073024287403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54358940439914715349524935 81538410659872073024287403)
  ·
    refine ⟨122307615989808109536431105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81538410659872073024287403 122307615989808109536431105)
    ·
      refine ⟨91730711992356082152323329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122307615989808109536431105 91730711992356082152323329)
      ·
        refine ⟨68798033994267061614242497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91730711992356082152323329 68798033994267061614242497)
        ·
          refine ⟨51598525495700296210681873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68798033994267061614242497 51598525495700296210681873)
          ·
            refine ⟨38698894121775222158011405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51598525495700296210681873 38698894121775222158011405)
            ·
              refine ⟨14512085295665708309254277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38698894121775222158011405 14512085295665708309254277)
              ·
                refine ⟨2721015992937320307985177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14512085295665708309254277 2721015992937320307985177)
                ·
                  refine ⟨2040761994702990230988883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2721015992937320307985177 2040761994702990230988883)
                  ·
                    refine ⟨3061142992054485346483325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040761994702990230988883 3061142992054485346483325)
                    ·
                      refine ⟨1147928622020432004931247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061142992054485346483325 1147928622020432004931247)
                      ·
                        rfl

theorem cell23_2235583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_2235583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235583 prefixEnd_2235583 := by exact prefixLift 2235583
  have htrace : WordTrace (prefixWord ++ tailWord_2235583) baseStart_2235583 baseEnd_2235583 := by
    simpa [prefixWord, tailWord_2235583, baseEnd_2235583] using wordTrace_append hprefix tailTrace_2235583
  have hstable : (prefixWord ++ tailWord_2235583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235583).length < 2 ^ (prefixWord ++ tailWord_2235583).sum := by decide
  have hdescent : baseEnd_2235583 < baseStart_2235583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235597 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2235597 : Nat := 118140960795 + 2235597 * 2 ^ 59
def prefixEnd_2235597 : Nat := 4983230072969 + 3 ^ 40 * 2235597 * 2
def baseEnd_2235597 : Nat := 1147935810749594950156183

theorem tailTrace_2235597 : CollatzResearch.WordTrace tailWord_2235597 prefixEnd_2235597 1147935810749594950156183 := by
  unfold tailWord_2235597
  simp only [CollatzResearch.WordTrace]
  refine ⟨81538921281821353415297045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54359280854547568943531363 81538921281821353415297045)
  ·
    refine ⟨3822136935085375941342049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81538921281821353415297045 3822136935085375941342049)
    ·
      refine ⟨2866602701314031956006537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3822136935085375941342049 2866602701314031956006537)
      ·
        refine ⟨2149952025985523967004903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2866602701314031956006537 2149952025985523967004903)
        ·
          refine ⟨3224928038978285950507355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149952025985523967004903 3224928038978285950507355)
          ·
            refine ⟨4837392058467428925761033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224928038978285950507355 4837392058467428925761033)
            ·
              refine ⟨3628044043850571694320775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4837392058467428925761033 3628044043850571694320775)
              ·
                refine ⟨5442066065775857541481163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628044043850571694320775 5442066065775857541481163)
                ·
                  refine ⟨8163099098663786312221745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442066065775857541481163 8163099098663786312221745)
                  ·
                    refine ⟨6122324323997839734166309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8163099098663786312221745 6122324323997839734166309)
                    ·
                      refine ⟨1147935810749594950156183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6122324323997839734166309 1147935810749594950156183)
                      ·
                        rfl

theorem cell23_2235597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2235597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235597 prefixEnd_2235597 := by exact prefixLift 2235597
  have htrace : WordTrace (prefixWord ++ tailWord_2235597) baseStart_2235597 baseEnd_2235597 := by
    simpa [prefixWord, tailWord_2235597, baseEnd_2235597] using wordTrace_append hprefix tailTrace_2235597
  have hstable : (prefixWord ++ tailWord_2235597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235597).length < 2 ^ (prefixWord ++ tailWord_2235597).sum := by decide
  have hdescent : baseEnd_2235597 < baseStart_2235597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235627 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 1, 3, 2]
def baseStart_2235627 : Nat := 118140960795 + 2235627 * 2 ^ 59
def prefixEnd_2235627 : Nat := 4983230072969 + 3 ^ 40 * 2235627 * 2
def baseEnd_2235627 : Nat := 1147951215169229832781045

theorem tailTrace_2235627 : CollatzResearch.WordTrace tailWord_2235627 prefixEnd_2235627 1147951215169229832781045 := by
  unfold tailWord_2235627
  simp only [CollatzResearch.WordTrace]
  refine ⟨81540015471712668538889135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54360010314475112359259423 81540015471712668538889135)
  ·
    refine ⟨122310023207569002808333703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81540015471712668538889135 122310023207569002808333703)
    ·
      refine ⟨183465034811353504212500555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122310023207569002808333703 183465034811353504212500555)
      ·
        refine ⟨275197552217030256318750833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183465034811353504212500555 275197552217030256318750833)
        ·
          refine ⟨206398164162772692239063125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275197552217030256318750833 206398164162772692239063125)
          ·
            refine ⟨2418728486282492487176521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 206398164162772692239063125 2418728486282492487176521)
            ·
              refine ⟨1814046364711869365382391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2418728486282492487176521 1814046364711869365382391)
              ·
                refine ⟨2721069547067804048073587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814046364711869365382391 2721069547067804048073587)
                ·
                  refine ⟨4081604320601706072110381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721069547067804048073587 4081604320601706072110381)
                  ·
                    refine ⟨1530601620225639777041393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4081604320601706072110381 1530601620225639777041393)
                    ·
                      refine ⟨1147951215169229832781045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530601620225639777041393 1147951215169229832781045)
                      ·
                        rfl

theorem cell23_2235627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 3, 2].length) (baseStart_2235627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235627 prefixEnd_2235627 := by exact prefixLift 2235627
  have htrace : WordTrace (prefixWord ++ tailWord_2235627) baseStart_2235627 baseEnd_2235627 := by
    simpa [prefixWord, tailWord_2235627, baseEnd_2235627] using wordTrace_append hprefix tailTrace_2235627
  have hstable : (prefixWord ++ tailWord_2235627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235627).length < 2 ^ (prefixWord ++ tailWord_2235627).sum := by decide
  have hdescent : baseEnd_2235627 < baseStart_2235627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235634 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2235634 : Nat := 118140960795 + 2235634 * 2 ^ 59
def prefixEnd_2235634 : Nat := 4983230072969 + 3 ^ 40 * 2235634 * 2
def baseEnd_2235634 : Nat := 1147954809533811305393513

theorem tailTrace_2235634 : CollatzResearch.WordTrace tailWord_2235634 prefixEnd_2235634 1147954809533811305393513 := by
  unfold tailWord_2235634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20385067695671827183598489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54360180521791539156262637 20385067695671827183598489)
  ·
    refine ⟨15288800771753870387698867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20385067695671827183598489 15288800771753870387698867)
    ·
      refine ⟨22933201157630805581548301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15288800771753870387698867 22933201157630805581548301)
      ·
        refine ⟨8599950434111552093080613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22933201157630805581548301 8599950434111552093080613)
        ·
          refine ⟨1612490706395916017452615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8599950434111552093080613 1612490706395916017452615)
          ·
            refine ⟨2418736059593874026178923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612490706395916017452615 2418736059593874026178923)
            ·
              refine ⟨3628104089390811039268385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418736059593874026178923 3628104089390811039268385)
              ·
                refine ⟨2721078067043108279451289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628104089390811039268385 2721078067043108279451289)
                ·
                  refine ⟨2040808550282331209588467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2721078067043108279451289 2040808550282331209588467)
                  ·
                    refine ⟨3061212825423496814382701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040808550282331209588467 3061212825423496814382701)
                    ·
                      refine ⟨1147954809533811305393513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061212825423496814382701 1147954809533811305393513)
                      ·
                        rfl

theorem cell23_2235634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2235634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235634 prefixEnd_2235634 := by exact prefixLift 2235634
  have htrace : WordTrace (prefixWord ++ tailWord_2235634) baseStart_2235634 baseEnd_2235634 := by
    simpa [prefixWord, tailWord_2235634, baseEnd_2235634] using wordTrace_append hprefix tailTrace_2235634
  have hstable : (prefixWord ++ tailWord_2235634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235634).length < 2 ^ (prefixWord ++ tailWord_2235634).sum := by decide
  have hdescent : baseEnd_2235634 < baseStart_2235634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235639 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_2235639 : Nat := 118140960795 + 2235639 * 2 ^ 59
def prefixEnd_2235639 : Nat := 4983230072969 + 3 ^ 40 * 2235639 * 2
def baseEnd_2235639 : Nat := 1147957376937083785830989

theorem tailTrace_2235639 : CollatzResearch.WordTrace tailWord_2235639 prefixEnd_2235639 1147957376937083785830989 := by
  unfold tailWord_2235639
  simp only [CollatzResearch.WordTrace]
  refine ⟨81540453147669194588325971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54360302098446129725550647 81540453147669194588325971)
  ·
    refine ⟨122310679721503791882488957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81540453147669194588325971 122310679721503791882488957)
    ·
      refine ⟨45866504895563921955933359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122310679721503791882488957 45866504895563921955933359)
      ·
        refine ⟨68799757343345882933900039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45866504895563921955933359 68799757343345882933900039)
        ·
          refine ⟨103199636015018824400850059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68799757343345882933900039 103199636015018824400850059)
          ·
            refine ⟨154799454022528236601275089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103199636015018824400850059 154799454022528236601275089)
            ·
              refine ⟨116099590516896177450956317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154799454022528236601275089 116099590516896177450956317)
              ·
                refine ⟨43537346443836066544108619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116099590516896177450956317 43537346443836066544108619)
                ·
                  refine ⟨65306019665754099816162929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43537346443836066544108619 65306019665754099816162929)
                  ·
                    refine ⟨48979514749315574862122197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65306019665754099816162929 48979514749315574862122197)
                    ·
                      refine ⟨1147957376937083785830989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48979514749315574862122197 1147957376937083785830989)
                      ·
                        rfl

theorem cell23_2235639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_2235639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235639 prefixEnd_2235639 := by exact prefixLift 2235639
  have htrace : WordTrace (prefixWord ++ tailWord_2235639) baseStart_2235639 baseEnd_2235639 := by
    simpa [prefixWord, tailWord_2235639, baseEnd_2235639] using wordTrace_append hprefix tailTrace_2235639
  have hstable : (prefixWord ++ tailWord_2235639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235639).length < 2 ^ (prefixWord ++ tailWord_2235639).sum := by decide
  have hdescent : baseEnd_2235639 < baseStart_2235639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235657 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 2, 2, 2]
def baseStart_2235657 : Nat := 118140960795 + 2235657 * 2 ^ 59
def prefixEnd_2235657 : Nat := 4983230072969 + 3 ^ 40 * 2235657 * 2
def baseEnd_2235657 : Nat := 1147966619588864715405907

theorem tailTrace_2235657 : CollatzResearch.WordTrace tailWord_2235657 prefixEnd_2235657 1147966619588864715405907 := by
  unfold tailWord_2235657
  simp only [CollatzResearch.WordTrace]
  refine ⟨81541109661603983662481225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54360739774402655774987483 81541109661603983662481225)
  ·
    refine ⟨61155832246202987746860919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81541109661603983662481225 61155832246202987746860919)
    ·
      refine ⟨91733748369304481620291379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61155832246202987746860919 91733748369304481620291379)
      ·
        refine ⟨137600622553956722430437069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91733748369304481620291379 137600622553956722430437069)
        ·
          refine ⟨51600233457733770911413901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137600622553956722430437069 51600233457733770911413901)
          ·
            refine ⟨19350087546650164091780213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51600233457733770911413901 19350087546650164091780213)
            ·
              refine ⟨1814070707498452883604395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19350087546650164091780213 1814070707498452883604395)
              ·
                refine ⟨2721106061247679325406593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814070707498452883604395 2721106061247679325406593)
                ·
                  refine ⟨2040829545935759494054945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2721106061247679325406593 2040829545935759494054945)
                  ·
                    refine ⟨1530622159451819620541209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2040829545935759494054945 1530622159451819620541209)
                    ·
                      refine ⟨1147966619588864715405907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530622159451819620541209 1147966619588864715405907)
                      ·
                        rfl

theorem cell23_2235657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 2, 2].length) (baseStart_2235657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235657 prefixEnd_2235657 := by exact prefixLift 2235657
  have htrace : WordTrace (prefixWord ++ tailWord_2235657) baseStart_2235657 baseEnd_2235657 := by
    simpa [prefixWord, tailWord_2235657, baseEnd_2235657] using wordTrace_append hprefix tailTrace_2235657
  have hstable : (prefixWord ++ tailWord_2235657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235657).length < 2 ^ (prefixWord ++ tailWord_2235657).sum := by decide
  have hdescent : baseEnd_2235657 < baseStart_2235657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235676 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_2235676 : Nat := 118140960795 + 2235676 * 2 ^ 59
def prefixEnd_2235676 : Nat := 4983230072969 + 3 ^ 40 * 2235676 * 2
def baseEnd_2235676 : Nat := 382658791907100047022773

theorem tailTrace_2235676 : CollatzResearch.WordTrace tailWord_2235676 prefixEnd_2235676 382658791907100047022773 := by
  unfold tailWord_2235676
  simp only [CollatzResearch.WordTrace]
  refine ⟨40770901324267574953711441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54361201765690099938281921 40770901324267574953711441)
  ·
    refine ⟨30578175993200681215283581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40770901324267574953711441 30578175993200681215283581)
    ·
      refine ⟨11466815997450255455731343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30578175993200681215283581 11466815997450255455731343)
      ·
        refine ⟨17200223996175383183597015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11466815997450255455731343 17200223996175383183597015)
        ·
          refine ⟨25800335994263074775395523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17200223996175383183597015 25800335994263074775395523)
          ·
            refine ⟨38700503991394612163093285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25800335994263074775395523 38700503991394612163093285)
            ·
              refine ⟨7256344498386489780579991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38700503991394612163093285 7256344498386489780579991)
              ·
                refine ⟨10884516747579734670869987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7256344498386489780579991 10884516747579734670869987)
                ·
                  refine ⟨16326775121369602006304981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10884516747579734670869987 16326775121369602006304981)
                  ·
                    refine ⟨382658791907100047022773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16326775121369602006304981 382658791907100047022773)
                    ·
                      rfl

theorem cell23_2235676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_2235676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235676 prefixEnd_2235676 := by exact prefixLift 2235676
  have htrace : WordTrace (prefixWord ++ tailWord_2235676) baseStart_2235676 baseEnd_2235676 := by
    simpa [prefixWord, tailWord_2235676, baseEnd_2235676] using wordTrace_append hprefix tailTrace_2235676
  have hstable : (prefixWord ++ tailWord_2235676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235676).length < 2 ^ (prefixWord ++ tailWord_2235676).sum := by decide
  have hdescent : baseEnd_2235676 < baseStart_2235676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235700 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_2235700 : Nat := 118140960795 + 2235700 * 2 ^ 59
def prefixEnd_2235700 : Nat := 4983230072969 + 3 ^ 40 * 2235700 * 2
def baseEnd_2235700 : Nat := 1147988699257008047168209

theorem tailTrace_2235700 : CollatzResearch.WordTrace tailWord_2235700 prefixEnd_2235700 1147988699257008047168209 := by
  unfold tailWord_2235700
  simp only [CollatzResearch.WordTrace]
  refine ⟨40771339000224101003148277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54361785333632134670864369 40771339000224101003148277)
  ·
    refine ⟨3822313031271009469045151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40771339000224101003148277 3822313031271009469045151)
    ·
      refine ⟨5733469546906514203567727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822313031271009469045151 5733469546906514203567727)
      ·
        refine ⟨8600204320359771305351591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5733469546906514203567727 8600204320359771305351591)
        ·
          refine ⟨12900306480539656958027387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8600204320359771305351591 12900306480539656958027387)
          ·
            refine ⟨19350459720809485437041081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12900306480539656958027387 19350459720809485437041081)
            ·
              refine ⟨14512844790607114077780811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19350459720809485437041081 14512844790607114077780811)
              ·
                refine ⟨21769267185910671116671217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14512844790607114077780811 21769267185910671116671217)
                ·
                  refine ⟨16326950389433003337503413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21769267185910671116671217 16326950389433003337503413)
                  ·
                    refine ⟨1530651599009344062890945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16326950389433003337503413 1530651599009344062890945)
                    ·
                      refine ⟨1147988699257008047168209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530651599009344062890945 1147988699257008047168209)
                      ·
                        rfl

theorem cell23_2235700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_2235700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235700 prefixEnd_2235700 := by exact prefixLift 2235700
  have htrace : WordTrace (prefixWord ++ tailWord_2235700) baseStart_2235700 baseEnd_2235700 := by
    simpa [prefixWord, tailWord_2235700, baseEnd_2235700] using wordTrace_append hprefix tailTrace_2235700
  have hstable : (prefixWord ++ tailWord_2235700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235700).length < 2 ^ (prefixWord ++ tailWord_2235700).sum := by decide
  have hdescent : baseEnd_2235700 < baseStart_2235700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235757 : List Nat := [1, 5, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_2235757 : Nat := 118140960795 + 2235757 * 2 ^ 59
def prefixEnd_2235757 : Nat := 4983230072969 + 3 ^ 40 * 2235757 * 2
def baseEnd_2235757 : Nat := 382672655884771441385149

theorem tailTrace_2235757 : CollatzResearch.WordTrace tailWord_2235757 prefixEnd_2235757 382672655884771441385149 := by
  unfold tailWord_2235757
  simp only [CollatzResearch.WordTrace]
  refine ⟨81544756961241700741121525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54363171307494467160747683 81544756961241700741121525)
  ·
    refine ⟨7644820965116409444480143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81544756961241700741121525 7644820965116409444480143)
    ·
      refine ⟨11467231447674614166720215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7644820965116409444480143 11467231447674614166720215)
      ·
        refine ⟨17200847171511921250080323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11467231447674614166720215 17200847171511921250080323)
        ·
          refine ⟨25801270757267881875120485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17200847171511921250080323 25801270757267881875120485)
          ·
            refine ⟨4837738266987727851585091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25801270757267881875120485 4837738266987727851585091)
            ·
              refine ⟨7256607400481591777377637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837738266987727851585091 7256607400481591777377637)
              ·
                refine ⟨1360613887590298458258307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7256607400481591777377637 1360613887590298458258307)
                ·
                  refine ⟨2040920831385447687387461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360613887590298458258307 2040920831385447687387461)
                  ·
                    refine ⟨382672655884771441385149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040920831385447687387461 382672655884771441385149)
                    ·
                      rfl

theorem cell23_2235757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_2235757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235757 prefixEnd_2235757 := by exact prefixLift 2235757
  have htrace : WordTrace (prefixWord ++ tailWord_2235757) baseStart_2235757 baseEnd_2235757 := by
    simpa [prefixWord, tailWord_2235757, baseEnd_2235757] using wordTrace_append hprefix tailTrace_2235757
  have hstable : (prefixWord ++ tailWord_2235757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235757).length < 2 ^ (prefixWord ++ tailWord_2235757).sum := by decide
  have hdescent : baseEnd_2235757 < baseStart_2235757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235774 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2235774 : Nat := 118140960795 + 2235774 * 2 ^ 59
def prefixEnd_2235774 : Nat := 4983230072969 + 3 ^ 40 * 2235774 * 2
def baseEnd_2235774 : Nat := 382675565608480252547623

theorem tailTrace_2235774 : CollatzResearch.WordTrace tailWord_2235774 prefixEnd_2235774 382675565608480252547623 := by
  unfold tailWord_2235774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10193172125272514080561297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54363584668120075096326917 10193172125272514080561297)
  ·
    refine ⟨7644879093954385560420973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10193172125272514080561297 7644879093954385560420973)
    ·
      refine ⟨2866829660232894585157865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7644879093954385560420973 2866829660232894585157865)
      ·
        refine ⟨2150122245174670938868399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2866829660232894585157865 2150122245174670938868399)
        ·
          refine ⟨3225183367762006408302599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2150122245174670938868399 3225183367762006408302599)
          ·
            refine ⟨4837775051643009612453899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3225183367762006408302599 4837775051643009612453899)
            ·
              refine ⟨7256662577464514418680849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837775051643009612453899 7256662577464514418680849)
              ·
                refine ⟨5442496933098385814010637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7256662577464514418680849 5442496933098385814010637)
                ·
                  refine ⟨2040936349911894680253989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5442496933098385814010637 2040936349911894680253989)
                  ·
                    refine ⟨382675565608480252547623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040936349911894680253989 382675565608480252547623)
                    ·
                      rfl

theorem cell23_2235774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2235774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235774 prefixEnd_2235774 := by exact prefixLift 2235774
  have htrace : WordTrace (prefixWord ++ tailWord_2235774) baseStart_2235774 baseEnd_2235774 := by
    simpa [prefixWord, tailWord_2235774, baseEnd_2235774] using wordTrace_append hprefix tailTrace_2235774
  have hstable : (prefixWord ++ tailWord_2235774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235774).length < 2 ^ (prefixWord ++ tailWord_2235774).sum := by decide
  have hdescent : baseEnd_2235774 < baseStart_2235774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235780 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_2235780 : Nat := 118140960795 + 2235780 * 2 ^ 59
def prefixEnd_2235780 : Nat := 4983230072969 + 3 ^ 40 * 2235780 * 2
def baseEnd_2235780 : Nat := 1148029777709367734167841

theorem tailTrace_2235780 : CollatzResearch.WordTrace tailWord_2235780 prefixEnd_2235780 1148029777709367734167841 := by
  unfold tailWord_2235780
  simp only [CollatzResearch.WordTrace]
  refine ⟨40772797920079187834604397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54363730560105583779472529 40772797920079187834604397)
  ·
    refine ⟨15289799220029695437976649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40772797920079187834604397 15289799220029695437976649)
    ·
      refine ⟨11467349415022271578482487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15289799220029695437976649 11467349415022271578482487)
      ·
        refine ⟨17201024122533407367723731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11467349415022271578482487 17201024122533407367723731)
        ·
          refine ⟨25801536183800111051585597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17201024122533407367723731 25801536183800111051585597)
          ·
            refine ⟨9675576068925041644344599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25801536183800111051585597 9675576068925041644344599)
            ·
              refine ⟨14513364103387562466516899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675576068925041644344599 14513364103387562466516899)
              ·
                refine ⟨21770046155081343699775349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14513364103387562466516899 21770046155081343699775349)
                ·
                  refine ⟨2040941827038875971853939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21770046155081343699775349 2040941827038875971853939)
                  ·
                    refine ⟨3061412740558313957780909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040941827038875971853939 3061412740558313957780909)
                    ·
                      refine ⟨1148029777709367734167841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061412740558313957780909 1148029777709367734167841)
                      ·
                        rfl

theorem cell23_2235780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_2235780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235780 prefixEnd_2235780 := by exact prefixLift 2235780
  have htrace : WordTrace (prefixWord ++ tailWord_2235780) baseStart_2235780 baseEnd_2235780 := by
    simpa [prefixWord, tailWord_2235780, baseEnd_2235780] using wordTrace_append hprefix tailTrace_2235780
  have hstable : (prefixWord ++ tailWord_2235780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235780).length < 2 ^ (prefixWord ++ tailWord_2235780).sum := by decide
  have hdescent : baseEnd_2235780 < baseStart_2235780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235783 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 3, 5]
def baseStart_2235783 : Nat := 118140960795 + 2235783 * 2 ^ 59
def prefixEnd_2235783 : Nat := 4983230072969 + 3 ^ 40 * 2235783 * 2
def baseEnd_2235783 : Nat := 382677106050443740810109

theorem tailTrace_2235783 : CollatzResearch.WordTrace tailWord_2235783 prefixEnd_2235783 382677106050443740810109 := by
  unfold tailWord_2235783
  simp only [CollatzResearch.WordTrace]
  refine ⟨81545705259147507181568003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54363803506098338121045335 81545705259147507181568003)
  ·
    refine ⟨122318557888721260772352005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81545705259147507181568003 122318557888721260772352005)
    ·
      refine ⟨22934729604135236394816001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122318557888721260772352005 22934729604135236394816001)
      ·
        refine ⟨17201047203101427296112001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22934729604135236394816001 17201047203101427296112001)
        ·
          refine ⟨12900785402326070472084001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17201047203101427296112001 12900785402326070472084001)
          ·
            refine ⟨9675589051744552854063001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12900785402326070472084001 9675589051744552854063001)
            ·
              refine ⟨7256691788808414640547251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9675589051744552854063001 7256691788808414640547251)
              ·
                refine ⟨10885037683212621960820877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7256691788808414640547251 10885037683212621960820877)
                ·
                  refine ⟨4081889131204733235307829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10885037683212621960820877 4081889131204733235307829)
                  ·
                    refine ⟨382677106050443740810109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4081889131204733235307829 382677106050443740810109)
                    ·
                      rfl

theorem cell23_2235783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_2235783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235783 prefixEnd_2235783 := by exact prefixLift 2235783
  have htrace : WordTrace (prefixWord ++ tailWord_2235783) baseStart_2235783 baseEnd_2235783 := by
    simpa [prefixWord, tailWord_2235783, baseEnd_2235783] using wordTrace_append hprefix tailTrace_2235783
  have hstable : (prefixWord ++ tailWord_2235783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235783).length < 2 ^ (prefixWord ++ tailWord_2235783).sum := by decide
  have hdescent : baseEnd_2235783 < baseStart_2235783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235797 : List Nat := [1, 3, 2, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_2235797 : Nat := 118140960795 + 2235797 * 2 ^ 59
def prefixEnd_2235797 : Nat := 4983230072969 + 3 ^ 40 * 2235797 * 2
def baseEnd_2235797 : Nat := 1148038506880494167655263

theorem tailTrace_2235797 : CollatzResearch.WordTrace tailWord_2235797 prefixEnd_2235797 1148038506880494167655263 := by
  unfold tailWord_2235797
  simp only [CollatzResearch.WordTrace]
  refine ⟨81546215881096787572577645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54364143920731191715051763 81546215881096787572577645)
  ·
    refine ⟨30579830955411295339716617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81546215881096787572577645 30579830955411295339716617)
    ·
      refine ⟨22934873216558471504787463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30579830955411295339716617 22934873216558471504787463)
      ·
        refine ⟨34402309824837707257181195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22934873216558471504787463 34402309824837707257181195)
        ·
          refine ⟨51603464737256560885771793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34402309824837707257181195 51603464737256560885771793)
          ·
            refine ⟨38702598552942420664328845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51603464737256560885771793 38702598552942420664328845)
            ·
              refine ⟨14513474457353407749123317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38702598552942420664328845 14513474457353407749123317)
              ·
                refine ⟨1360638230376881976480311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14513474457353407749123317 1360638230376881976480311)
                ·
                  refine ⟨2040957345565322964720467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360638230376881976480311 2040957345565322964720467)
                  ·
                    refine ⟨3061436018347984447080701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2040957345565322964720467 3061436018347984447080701)
                    ·
                      refine ⟨1148038506880494167655263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061436018347984447080701 1148038506880494167655263)
                      ·
                        rfl

theorem cell23_2235797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_2235797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235797 prefixEnd_2235797 := by exact prefixLift 2235797
  have htrace : WordTrace (prefixWord ++ tailWord_2235797) baseStart_2235797 baseEnd_2235797 := by
    simpa [prefixWord, tailWord_2235797, baseEnd_2235797] using wordTrace_append hprefix tailTrace_2235797
  have hstable : (prefixWord ++ tailWord_2235797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235797).length < 2 ^ (prefixWord ++ tailWord_2235797).sum := by decide
  have hdescent : baseEnd_2235797 < baseStart_2235797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 6, 6, 2]
def baseStart_2235803 : Nat := 118140960795 + 2235803 * 2 ^ 59
def prefixEnd_2235803 : Nat := 4983230072969 + 3 ^ 40 * 2235803 * 2
def baseEnd_2235803 : Nat := 1148041587764421144180235

theorem tailTrace_2235803 : CollatzResearch.WordTrace tailWord_2235803 prefixEnd_2235803 1148041587764421144180235 := by
  unfold tailWord_2235803
  simp only [CollatzResearch.WordTrace]
  refine ⟨81546434719075050597296063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54364289812716700398197375 81546434719075050597296063)
  ·
    refine ⟨122319652078612575895944095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81546434719075050597296063 122319652078612575895944095)
    ·
      refine ⟨183479478117918863843916143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122319652078612575895944095 183479478117918863843916143)
      ·
        refine ⟨275219217176878295765874215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183479478117918863843916143 275219217176878295765874215)
        ·
          refine ⟨412828825765317443648811323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275219217176878295765874215 412828825765317443648811323)
          ·
            refine ⟨619243238647976165473216985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412828825765317443648811323 619243238647976165473216985)
            ·
              refine ⟨464432428985982124104912739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619243238647976165473216985 464432428985982124104912739)
              ·
                refine ⟨696648643478973186157369109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464432428985982124104912739 696648643478973186157369109)
                ·
                  refine ⟨32655405163076868101126677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 696648643478973186157369109 32655405163076868101126677)
                  ·
                    refine ⟨1530722117019228192240313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32655405163076868101126677 1530722117019228192240313)
                    ·
                      refine ⟨1148041587764421144180235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530722117019228192240313 1148041587764421144180235)
                      ·
                        rfl

theorem cell23_2235803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6, 2].length) (baseStart_2235803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235803 prefixEnd_2235803 := by exact prefixLift 2235803
  have htrace : WordTrace (prefixWord ++ tailWord_2235803) baseStart_2235803 baseEnd_2235803 := by
    simpa [prefixWord, tailWord_2235803, baseEnd_2235803] using wordTrace_append hprefix tailTrace_2235803
  have hstable : (prefixWord ++ tailWord_2235803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235803).length < 2 ^ (prefixWord ++ tailWord_2235803).sum := by decide
  have hdescent : baseEnd_2235803 < baseStart_2235803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235804 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 6]
def baseStart_2235804 : Nat := 118140960795 + 2235804 * 2 ^ 59
def prefixEnd_2235804 : Nat := 4983230072969 + 3 ^ 40 * 2235804 * 2
def baseEnd_2235804 : Nat := 127560233471675071140859

theorem tailTrace_2235804 : CollatzResearch.WordTrace tailWord_2235804 prefixEnd_2235804 127560233471675071140859 := by
  unfold tailWord_2235804
  simp only [CollatzResearch.WordTrace]
  refine ⟨40773235596035713884041233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54364314128047618512054977 40773235596035713884041233)
  ·
    refine ⟨30579926697026785413030925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40773235596035713884041233 30579926697026785413030925)
    ·
      refine ⟨11467472511385044529886597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30579926697026785413030925 11467472511385044529886597)
      ·
        refine ⟨2150151095884695849353737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11467472511385044529886597 2150151095884695849353737)
        ·
          refine ⟨1612613321913521887015303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150151095884695849353737 1612613321913521887015303)
          ·
            refine ⟨2418919982870282830522955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612613321913521887015303 2418919982870282830522955)
            ·
              refine ⟨3628379974305424245784433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418919982870282830522955 3628379974305424245784433)
              ·
                refine ⟨2721284980729068184338325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628379974305424245784433 2721284980729068184338325)
                ·
                  refine ⟨127560233471675071140859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2721284980729068184338325 127560233471675071140859)
                  ·
                    rfl

theorem cell23_2235804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_2235804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235804 prefixEnd_2235804 := by exact prefixLift 2235804
  have htrace : WordTrace (prefixWord ++ tailWord_2235804) baseStart_2235804 baseEnd_2235804 := by
    simpa [prefixWord, tailWord_2235804, baseEnd_2235804] using wordTrace_append hprefix tailTrace_2235804
  have hstable : (prefixWord ++ tailWord_2235804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235804).length < 2 ^ (prefixWord ++ tailWord_2235804).sum := by decide
  have hdescent : baseEnd_2235804 < baseStart_2235804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235823 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 3]
def baseStart_2235823 : Nat := 118140960795 + 2235823 * 2 ^ 59
def prefixEnd_2235823 : Nat := 4983230072969 + 3 ^ 40 * 2235823 * 2
def baseEnd_2235823 : Nat := 1148051857377511065930143

theorem tailTrace_2235823 : CollatzResearch.WordTrace tailWord_2235823 prefixEnd_2235823 1148051857377511065930143 := by
  unfold tailWord_2235823
  simp only [CollatzResearch.WordTrace]
  refine ⟨81547164179002594013024123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54364776119335062675349415 81547164179002594013024123)
  ·
    refine ⟨122320746268503891019536185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81547164179002594013024123 122320746268503891019536185)
    ·
      refine ⟨91740559701377918264652139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122320746268503891019536185 91740559701377918264652139)
      ·
        refine ⟨137610839552066877396978209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91740559701377918264652139 137610839552066877396978209)
        ·
          refine ⟨103208129664050158047733657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137610839552066877396978209 103208129664050158047733657)
          ·
            refine ⟨77406097248037618535800243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103208129664050158047733657 77406097248037618535800243)
            ·
              refine ⟨116109145872056427803700365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77406097248037618535800243 116109145872056427803700365)
              ·
                refine ⟨43540929702021160426387637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116109145872056427803700365 43540929702021160426387637)
                ·
                  refine ⟨4081962159564483789973841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43540929702021160426387637 4081962159564483789973841)
                  ·
                    refine ⟨3061471619673362842480381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4081962159564483789973841 3061471619673362842480381)
                    ·
                      refine ⟨1148051857377511065930143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061471619673362842480381 1148051857377511065930143)
                      ·
                        rfl

theorem cell23_2235823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_2235823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235823 prefixEnd_2235823 := by exact prefixLift 2235823
  have htrace : WordTrace (prefixWord ++ tailWord_2235823) baseStart_2235823 baseEnd_2235823 := by
    simpa [prefixWord, tailWord_2235823, baseEnd_2235823] using wordTrace_append hprefix tailTrace_2235823
  have hstable : (prefixWord ++ tailWord_2235823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235823).length < 2 ^ (prefixWord ++ tailWord_2235823).sum := by decide
  have hdescent : baseEnd_2235823 < baseStart_2235823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235837 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_2235837 : Nat := 118140960795 + 2235837 * 2 ^ 59
def prefixEnd_2235837 : Nat := 4983230072969 + 3 ^ 40 * 2235837 * 2
def baseEnd_2235837 : Nat := 1148059046106674011155079

theorem tailTrace_2235837 : CollatzResearch.WordTrace tailWord_2235837 prefixEnd_2235837 1148059046106674011155079 := by
  unfold tailWord_2235837
  simp only [CollatzResearch.WordTrace]
  refine ⟨81547674800951874404033765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54365116533967916269355843 81547674800951874404033765)
  ·
    refine ⟨15290189025178476450756331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81547674800951874404033765 15290189025178476450756331)
    ·
      refine ⟨22935283537767714676134497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15290189025178476450756331 22935283537767714676134497)
      ·
        refine ⟨17201462653325786007100873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22935283537767714676134497 17201462653325786007100873)
        ·
          refine ⟨12901096989994339505325655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17201462653325786007100873 12901096989994339505325655)
          ·
            refine ⟨19351645484991509257988483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12901096989994339505325655 19351645484991509257988483)
            ·
              refine ⟨29027468227487263886982725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19351645484991509257988483 29027468227487263886982725)
              ·
                refine ⟨5442650292653861978809261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29027468227487263886982725 5442650292653861978809261)
                ·
                  refine ⟨2040993859745198242053473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5442650292653861978809261 2040993859745198242053473)
                  ·
                    refine ⟨1530745394808898681540105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2040993859745198242053473 1530745394808898681540105)
                    ·
                      refine ⟨1148059046106674011155079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530745394808898681540105 1148059046106674011155079)
                      ·
                        rfl

theorem cell23_2235837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_2235837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235837 prefixEnd_2235837 := by exact prefixLift 2235837
  have htrace : WordTrace (prefixWord ++ tailWord_2235837) baseStart_2235837 baseEnd_2235837 := by
    simpa [prefixWord, tailWord_2235837, baseEnd_2235837] using wordTrace_append hprefix tailTrace_2235837
  have hstable : (prefixWord ++ tailWord_2235837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235837).length < 2 ^ (prefixWord ++ tailWord_2235837).sum := by decide
  have hdescent : baseEnd_2235837 < baseStart_2235837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235840 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3]
def baseStart_2235840 : Nat := 118140960795 + 2235840 * 2 ^ 59
def prefixEnd_2235840 : Nat := 4983230072969 + 3 ^ 40 * 2235840 * 2
def baseEnd_2235840 : Nat := 1148060586548637499417565

theorem tailTrace_2235840 : CollatzResearch.WordTrace tailWord_2235840 prefixEnd_2235840 1148060586548637499417565 := by
  unfold tailWord_2235840
  simp only [CollatzResearch.WordTrace]
  refine ⟨40773892109970502958196487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54365189479960670610928649 40773892109970502958196487)
  ·
    refine ⟨61160838164955754437294731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40773892109970502958196487 61160838164955754437294731)
    ·
      refine ⟨91741257247433631655942097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61160838164955754437294731 91741257247433631655942097)
      ·
        refine ⟨68805942935575223741956573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91741257247433631655942097 68805942935575223741956573)
        ·
          refine ⟨25802228600840708903233715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68805942935575223741956573 25802228600840708903233715)
          ·
            refine ⟨38703342901261063354850573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25802228600840708903233715 38703342901261063354850573)
            ·
              refine ⟨14513753587972898758068965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38703342901261063354850573 14513753587972898758068965)
              ·
                refine ⟨2721328797744918517137931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14513753587972898758068965 2721328797744918517137931)
                ·
                  refine ⟨4081993196617377775706897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721328797744918517137931 4081993196617377775706897)
                  ·
                    refine ⟨3061494897463033331780173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4081993196617377775706897 3061494897463033331780173)
                    ·
                      refine ⟨1148060586548637499417565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061494897463033331780173 1148060586548637499417565)
                      ·
                        rfl

theorem cell23_2235840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_2235840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235840 prefixEnd_2235840 := by exact prefixLift 2235840
  have htrace : WordTrace (prefixWord ++ tailWord_2235840) baseStart_2235840 baseEnd_2235840 := by
    simpa [prefixWord, tailWord_2235840, baseEnd_2235840] using wordTrace_append hprefix tailTrace_2235840
  have hstable : (prefixWord ++ tailWord_2235840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235840).length < 2 ^ (prefixWord ++ tailWord_2235840).sum := by decide
  have hdescent : baseEnd_2235840 < baseStart_2235840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235842 : List Nat := [3, 5, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2235842 : Nat := 118140960795 + 2235842 * 2 ^ 59
def prefixEnd_2235842 : Nat := 4983230072969 + 3 ^ 40 * 2235842 * 2
def baseEnd_2235842 : Nat := 382687204503315497197519

theorem tailTrace_2235842 : CollatzResearch.WordTrace tailWord_2235842 prefixEnd_2235842 382687204503315497197519 := by
  unfold tailWord_2235842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20386964291483440064491445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54365238110622506838643853 20386964291483440064491445)
  ·
    refine ⟨1911277902326572506046073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20386964291483440064491445 1911277902326572506046073)
    ·
      refine ⟨1433458426744929379534555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1911277902326572506046073 1433458426744929379534555)
      ·
        refine ⟨2150187640117394069301833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433458426744929379534555 2150187640117394069301833)
        ·
          refine ⟨1612640730088045551976375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150187640117394069301833 1612640730088045551976375)
          ·
            refine ⟨2418961095132068327964563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612640730088045551976375 2418961095132068327964563)
            ·
              refine ⟨3628441642698102491946845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418961095132068327964563 3628441642698102491946845)
              ·
                refine ⟨1360665616011788434480067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3628441642698102491946845 1360665616011788434480067)
                ·
                  refine ⟨2040998424017682651720101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360665616011788434480067 2040998424017682651720101)
                  ·
                    refine ⟨382687204503315497197519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040998424017682651720101 382687204503315497197519)
                    ·
                      rfl

theorem cell23_2235842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2235842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235842 prefixEnd_2235842 := by exact prefixLift 2235842
  have htrace : WordTrace (prefixWord ++ tailWord_2235842) baseStart_2235842 baseEnd_2235842 := by
    simpa [prefixWord, tailWord_2235842, baseEnd_2235842] using wordTrace_append hprefix tailTrace_2235842
  have hstable : (prefixWord ++ tailWord_2235842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235842).length < 2 ^ (prefixWord ++ tailWord_2235842).sum := by decide
  have hdescent : baseEnd_2235842 < baseStart_2235842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235843 : List Nat := [1, 1, 1, 3, 1, 1, 8, 7]
def baseStart_2235843 : Nat := 118140960795 + 2235843 * 2 ^ 59
def prefixEnd_2235843 : Nat := 4983230072969 + 3 ^ 40 * 2235843 * 2
def baseEnd_2235843 : Nat := 42520819518170406951113

theorem tailTrace_2235843 : CollatzResearch.WordTrace tailWord_2235843 prefixEnd_2235843 42520819518170406951113 := by
  unfold tailWord_2235843
  simp only [CollatzResearch.WordTrace]
  refine ⟨81547893638930137428752183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54365262425953424952501455 81547893638930137428752183)
  ·
    refine ⟨122321840458395206143128275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81547893638930137428752183 122321840458395206143128275)
    ·
      refine ⟨183482760687592809214692413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122321840458395206143128275 183482760687592809214692413)
      ·
        refine ⟨68806035257847303455509655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183482760687592809214692413 68806035257847303455509655)
        ·
          refine ⟨103209052886770955183264483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68806035257847303455509655 103209052886770955183264483)
          ·
            refine ⟨154813579330156432774896725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103209052886770955183264483 154813579330156432774896725)
            ·
              refine ⟨1814221632775270696580821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 154813579330156432774896725 1814221632775270696580821)
              ·
                refine ⟨42520819518170406951113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1814221632775270696580821 42520819518170406951113)
                ·
                  rfl

theorem cell23_2235843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 7].length) (baseStart_2235843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235843 prefixEnd_2235843 := by exact prefixLift 2235843
  have htrace : WordTrace (prefixWord ++ tailWord_2235843) baseStart_2235843 baseEnd_2235843 := by
    simpa [prefixWord, tailWord_2235843, baseEnd_2235843] using wordTrace_append hprefix tailTrace_2235843
  have hstable : (prefixWord ++ tailWord_2235843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235843).length < 2 ^ (prefixWord ++ tailWord_2235843).sum := by decide
  have hdescent : baseEnd_2235843 < baseStart_2235843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235860 : List Nat := [2, 4, 1, 2, 3, 2, 9]
def baseStart_2235860 : Nat := 118140960795 + 2235860 * 2 ^ 59
def prefixEnd_2235860 : Nat := 4983230072969 + 3 ^ 40 * 2235860 * 2
def baseEnd_2235860 : Nat := 14173714273601573100833

theorem tailTrace_2235860 : CollatzResearch.WordTrace tailWord_2235860 prefixEnd_2235860 14173714273601573100833 := by
  unfold tailWord_2235860
  simp only [CollatzResearch.WordTrace]
  refine ⟨40774256839934274666060517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54365675786579032888080689 40774256839934274666060517)
  ·
    refine ⟨7645173157487676499886347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40774256839934274666060517 7645173157487676499886347)
    ·
      refine ⟨11467759736231514749829521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645173157487676499886347 11467759736231514749829521)
      ·
        refine ⟨8600819802173636062372141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11467759736231514749829521 8600819802173636062372141)
        ·
          refine ⟨3225307425815113523389553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8600819802173636062372141 3225307425815113523389553)
          ·
            refine ⟨2418980569361335142542165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3225307425815113523389553 2418980569361335142542165)
            ·
              refine ⟨14173714273601573100833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2418980569361335142542165 14173714273601573100833)
              ·
                rfl

theorem cell23_2235860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 9].length) (baseStart_2235860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235860 prefixEnd_2235860 := by exact prefixLift 2235860
  have htrace : WordTrace (prefixWord ++ tailWord_2235860) baseStart_2235860 baseEnd_2235860 := by
    simpa [prefixWord, tailWord_2235860, baseEnd_2235860] using wordTrace_append hprefix tailTrace_2235860
  have hstable : (prefixWord ++ tailWord_2235860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235860).length < 2 ^ (prefixWord ++ tailWord_2235860).sum := by decide
  have hdescent : baseEnd_2235860 < baseStart_2235860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235871 : List Nat := [1, 1, 2, 3, 3, 1, 5, 2, 1, 2, 2]
def baseStart_2235871 : Nat := 118140960795 + 2235871 * 2 ^ 59
def prefixEnd_2235871 : Nat := 4983230072969 + 3 ^ 40 * 2235871 * 2
def baseEnd_2235871 : Nat := 1148076504448926878129923

theorem tailTrace_2235871 : CollatzResearch.WordTrace tailWord_2235871 prefixEnd_2235871 1148076504448926878129923 := by
  unfold tailWord_2235871
  simp only [CollatzResearch.WordTrace]
  refine ⟨81548914882828698210771467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54365943255219132140514311 81548914882828698210771467)
  ·
    refine ⟨122323372324243047316157201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81548914882828698210771467 122323372324243047316157201)
    ·
      refine ⟨91742529243182285487117901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122323372324243047316157201 91742529243182285487117901)
      ·
        refine ⟨34403448466193357057669213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91742529243182285487117901 34403448466193357057669213)
        ·
          refine ⟨12901293174822508896625955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34403448466193357057669213 12901293174822508896625955)
          ·
            refine ⟨19351939762233763344938933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12901293174822508896625955 19351939762233763344938933)
            ·
              refine ⟨1814244352709415313588025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19351939762233763344938933 1814244352709415313588025)
              ·
                refine ⟨1360683264532061485191019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814244352709415313588025 1360683264532061485191019)
                ·
                  refine ⟨2041024896798092227786529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360683264532061485191019 2041024896798092227786529)
                  ·
                    refine ⟨1530768672598569170839897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2041024896798092227786529 1530768672598569170839897)
                    ·
                      refine ⟨1148076504448926878129923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530768672598569170839897 1148076504448926878129923)
                      ·
                        rfl

theorem cell23_2235871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_2235871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235871 prefixEnd_2235871 := by exact prefixLift 2235871
  have htrace : WordTrace (prefixWord ++ tailWord_2235871) baseStart_2235871 baseEnd_2235871 := by
    simpa [prefixWord, tailWord_2235871, baseEnd_2235871] using wordTrace_append hprefix tailTrace_2235871
  have hstable : (prefixWord ++ tailWord_2235871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235871).length < 2 ^ (prefixWord ++ tailWord_2235871).sum := by decide
  have hdescent : baseEnd_2235871 < baseStart_2235871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235913 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_2235913 : Nat := 118140960795 + 2235913 * 2 ^ 59
def prefixEnd_2235913 : Nat := 4983230072969 + 3 ^ 40 * 2235913 * 2
def baseEnd_2235913 : Nat := 1148098070636415713804729

theorem tailTrace_2235913 : CollatzResearch.WordTrace tailWord_2235913 prefixEnd_2235913 1148098070636415713804729 := by
  unfold tailWord_2235913
  simp only [CollatzResearch.WordTrace]
  refine ⟨81550446748676539383800393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54366964499117692922533595 81550446748676539383800393)
  ·
    refine ⟨61162835061507404537850295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81550446748676539383800393 61162835061507404537850295)
    ·
      refine ⟨91744252592261106806775443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61162835061507404537850295 91744252592261106806775443)
      ·
        refine ⟨137616378888391660210163165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91744252592261106806775443 137616378888391660210163165)
        ·
          refine ⟨51606142083146872578811187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137616378888391660210163165 51606142083146872578811187)
          ·
            refine ⟨77409213124720308868216781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51606142083146872578811187 77409213124720308868216781)
            ·
              refine ⟨29028454921770115825581293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77409213124720308868216781 29028454921770115825581293)
              ·
                refine ⟨10885670595663793434592985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29028454921770115825581293 10885670595663793434592985)
                ·
                  refine ⟨8164252946747845075944739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10885670595663793434592985 8164252946747845075944739)
                  ·
                    refine ⟨12246379420121767613917109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8164252946747845075944739 12246379420121767613917109)
                    ·
                      refine ⟨1148098070636415713804729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12246379420121767613917109 1148098070636415713804729)
                      ·
                        rfl

theorem cell23_2235913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_2235913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235913 prefixEnd_2235913 := by exact prefixLift 2235913
  have htrace : WordTrace (prefixWord ++ tailWord_2235913) baseStart_2235913 baseEnd_2235913 := by
    simpa [prefixWord, tailWord_2235913, baseEnd_2235913] using wordTrace_append hprefix tailTrace_2235913
  have hstable : (prefixWord ++ tailWord_2235913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235913).length < 2 ^ (prefixWord ++ tailWord_2235913).sum := by decide
  have hdescent : baseEnd_2235913 < baseStart_2235913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235950 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_2235950 : Nat := 118140960795 + 2235950 * 2 ^ 59
def prefixEnd_2235950 : Nat := 4983230072969 + 3 ^ 40 * 2235950 * 2
def baseEnd_2235950 : Nat := 127568563268959118782451

theorem tailTrace_2235950 : CollatzResearch.WordTrace tailWord_2235950 prefixEnd_2235950 127568563268959118782451 := by
  unfold tailWord_2235950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10193974531192811837862163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54367864166361663135264869 10193974531192811837862163)
  ·
    refine ⟨15290961796789217756793245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10193974531192811837862163 15290961796789217756793245)
    ·
      refine ⟨5734110673795956658797467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15290961796789217756793245 5734110673795956658797467)
      ·
        refine ⟨8601166010693934988196201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5734110673795956658797467 8601166010693934988196201)
        ·
          refine ⟨6450874508020451241147151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8601166010693934988196201 6450874508020451241147151)
          ·
            refine ⟨9676311762030676861720727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450874508020451241147151 9676311762030676861720727)
            ·
              refine ⟨14514467643046015292581091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9676311762030676861720727 14514467643046015292581091)
              ·
                refine ⟨21771701464569022938871637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14514467643046015292581091 21771701464569022938871637)
                ·
                  refine ⟨127568563268959118782451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21771701464569022938871637 127568563268959118782451)
                  ·
                    rfl

theorem cell23_2235950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_2235950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235950 prefixEnd_2235950 := by exact prefixLift 2235950
  have htrace : WordTrace (prefixWord ++ tailWord_2235950) baseStart_2235950 baseEnd_2235950 := by
    simpa [prefixWord, tailWord_2235950, baseEnd_2235950] using wordTrace_append hprefix tailTrace_2235950
  have hstable : (prefixWord ++ tailWord_2235950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235950).length < 2 ^ (prefixWord ++ tailWord_2235950).sum := by decide
  have hdescent : baseEnd_2235950 < baseStart_2235950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235967 : List Nat := [1, 1, 2, 2, 3, 4, 2, 3, 5]
def baseStart_2235967 : Nat := 118140960795 + 2235967 * 2 ^ 59
def prefixEnd_2235967 : Nat := 4983230072969 + 3 ^ 40 * 2235967 * 2
def baseEnd_2235967 : Nat := 127569533176862055836609

theorem tailTrace_2235967 : CollatzResearch.WordTrace tailWord_2235967 prefixEnd_2235967 127569533176862055836609 := by
  unfold tailWord_2235967
  simp only [CollatzResearch.WordTrace]
  refine ⟨81552416290480906606266155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54368277526987271070844103 81552416290480906606266155)
  ·
    refine ⟨122328624435721359909399233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81552416290480906606266155 122328624435721359909399233)
    ·
      refine ⟨91746468326791019932049425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122328624435721359909399233 91746468326791019932049425)
      ·
        refine ⟨68809851245093264949037069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91746468326791019932049425 68809851245093264949037069)
        ·
          refine ⟨25803694216909974355888901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68809851245093264949037069 25803694216909974355888901)
          ·
            refine ⟨4838192665670620191729169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25803694216909974355888901 4838192665670620191729169)
            ·
              refine ⟨3628644499252965143796877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838192665670620191729169 3628644499252965143796877)
              ·
                refine ⟨1360741687219861928923829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3628644499252965143796877 1360741687219861928923829)
                ·
                  refine ⟨127569533176862055836609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1360741687219861928923829 127569533176862055836609)
                  ·
                    rfl

theorem cell23_2235967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 5].length) (baseStart_2235967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2235967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2235967 prefixEnd_2235967 := by exact prefixLift 2235967
  have htrace : WordTrace (prefixWord ++ tailWord_2235967) baseStart_2235967 baseEnd_2235967 := by
    simpa [prefixWord, tailWord_2235967, baseEnd_2235967] using wordTrace_append hprefix tailTrace_2235967
  have hstable : (prefixWord ++ tailWord_2235967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235967).length < 2 ^ (prefixWord ++ tailWord_2235967).sum := by decide
  have hdescent : baseEnd_2235967 < baseStart_2235967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236037 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_2236037 : Nat := 118140960795 + 2236037 * 2 ^ 59
def prefixEnd_2236037 : Nat := 4983230072969 + 3 ^ 40 * 2236037 * 2
def baseEnd_2236037 : Nat := 1148161742237573228654159

theorem tailTrace_2236037 : CollatzResearch.WordTrace tailWord_2236037 prefixEnd_2236037 1148161742237573228654159 := by
  unfold tailWord_2236037
  simp only [CollatzResearch.WordTrace]
  refine ⟨81554969400227308561314365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54369979600151539040876243 81554969400227308561314365)
  ·
    refine ⟨30583113525085240710492887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81554969400227308561314365 30583113525085240710492887)
    ·
      refine ⟨45874670287627861065739331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30583113525085240710492887 45874670287627861065739331)
      ·
        refine ⟨68812005431441791598608997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45874670287627861065739331 68812005431441791598608997)
        ·
          refine ⟨12902251018395335924739187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68812005431441791598608997 12902251018395335924739187)
          ·
            refine ⟨19353376527593003887108781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12902251018395335924739187 19353376527593003887108781)
            ·
              refine ⟨7257516197847376457665793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19353376527593003887108781 7257516197847376457665793)
              ·
                refine ⟨5443137148385532343249345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7257516197847376457665793 5443137148385532343249345)
                ·
                  refine ⟨4082352861289149257437009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5443137148385532343249345 4082352861289149257437009)
                  ·
                    refine ⟨3061764645966861943077757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4082352861289149257437009 3061764645966861943077757)
                    ·
                      refine ⟨1148161742237573228654159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061764645966861943077757 1148161742237573228654159)
                      ·
                        rfl

theorem cell23_2236037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_2236037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236037 prefixEnd_2236037 := by exact prefixLift 2236037
  have htrace : WordTrace (prefixWord ++ tailWord_2236037) baseStart_2236037 baseEnd_2236037 := by
    simpa [prefixWord, tailWord_2236037, baseEnd_2236037] using wordTrace_append hprefix tailTrace_2236037
  have hstable : (prefixWord ++ tailWord_2236037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236037).length < 2 ^ (prefixWord ++ tailWord_2236037).sum := by decide
  have hdescent : baseEnd_2236037 < baseStart_2236037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236067 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 3]
def baseStart_2236067 : Nat := 118140960795 + 2236067 * 2 ^ 59
def prefixEnd_2236067 : Nat := 4983230072969 + 3 ^ 40 * 2236067 * 2
def baseEnd_2236067 : Nat := 1148177146657208111279021

theorem tailTrace_2236067 : CollatzResearch.WordTrace tailWord_2236067 prefixEnd_2236067 1148177146657208111279021 := by
  unfold tailWord_2236067
  simp only [CollatzResearch.WordTrace]
  refine ⟨81556063590118623684906455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54370709060079082456604303 81556063590118623684906455)
  ·
    refine ⟨122334095385177935527359683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81556063590118623684906455 122334095385177935527359683)
    ·
      refine ⟨183501143077766903291039525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122334095385177935527359683 183501143077766903291039525)
      ·
        refine ⟨34406464327081294367069911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183501143077766903291039525 34406464327081294367069911)
        ·
          refine ⟨51609696490621941550604867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34406464327081294367069911 51609696490621941550604867)
          ·
            refine ⟨77414544735932912325907301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51609696490621941550604867 77414544735932912325907301)
            ·
              refine ⟨14515227137987421061107619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77414544735932912325907301 14515227137987421061107619)
              ·
                refine ⟨21772840706981131591661429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14515227137987421061107619 21772840706981131591661429)
                ·
                  refine ⟨2041203816279481086718259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21772840706981131591661429 2041203816279481086718259)
                  ·
                    refine ⟨3061805724419221630077389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2041203816279481086718259 3061805724419221630077389)
                    ·
                      refine ⟨1148177146657208111279021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061805724419221630077389 1148177146657208111279021)
                      ·
                        rfl

theorem cell23_2236067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_2236067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236067 prefixEnd_2236067 := by exact prefixLift 2236067
  have htrace : WordTrace (prefixWord ++ tailWord_2236067) baseStart_2236067 baseEnd_2236067 := by
    simpa [prefixWord, tailWord_2236067, baseEnd_2236067] using wordTrace_append hprefix tailTrace_2236067
  have hstable : (prefixWord ++ tailWord_2236067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236067).length < 2 ^ (prefixWord ++ tailWord_2236067).sum := by decide
  have hdescent : baseEnd_2236067 < baseStart_2236067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236127 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 3]
def baseStart_2236127 : Nat := 118140960795 + 2236127 * 2 ^ 59
def prefixEnd_2236127 : Nat := 4983230072969 + 3 ^ 40 * 2236127 * 2
def baseEnd_2236127 : Nat := 1148207955496477876528745

theorem tailTrace_2236127 : CollatzResearch.WordTrace tailWord_2236127 prefixEnd_2236127 1148207955496477876528745 := by
  unfold tailWord_2236127
  simp only [CollatzResearch.WordTrace]
  refine ⟨81558251969901253932090635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54372167979934169288060423 81558251969901253932090635)
  ·
    refine ⟨122337377954851880898135953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81558251969901253932090635 122337377954851880898135953)
    ·
      refine ⟨91753033466138910673601965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122337377954851880898135953 91753033466138910673601965)
      ·
        refine ⟨34407387549802091502600737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91753033466138910673601965 34407387549802091502600737)
        ·
          refine ⟨25805540662351568626950553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34407387549802091502600737 25805540662351568626950553)
          ·
            refine ⟨19354155496763676470212915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25805540662351568626950553 19354155496763676470212915)
            ·
              refine ⟨29031233245145514705319373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19354155496763676470212915 29031233245145514705319373)
              ·
                refine ⟨10886712466929568014494765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29031233245145514705319373 10886712466929568014494765)
                ·
                  refine ⟨4082517175098588005435537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10886712466929568014494765 4082517175098588005435537)
                  ·
                    refine ⟨3061887881323941004076653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4082517175098588005435537 3061887881323941004076653)
                    ·
                      refine ⟨1148207955496477876528745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061887881323941004076653 1148207955496477876528745)
                      ·
                        rfl

theorem cell23_2236127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_2236127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236127 prefixEnd_2236127 := by exact prefixLift 2236127
  have htrace : WordTrace (prefixWord ++ tailWord_2236127) baseStart_2236127 baseEnd_2236127 := by
    simpa [prefixWord, tailWord_2236127, baseEnd_2236127] using wordTrace_append hprefix tailTrace_2236127
  have hstable : (prefixWord ++ tailWord_2236127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236127).length < 2 ^ (prefixWord ++ tailWord_2236127).sum := by decide
  have hdescent : baseEnd_2236127 < baseStart_2236127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236135 : List Nat := [1, 1, 5, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2236135 : Nat := 118140960795 + 2236135 * 2 ^ 59
def prefixEnd_2236135 : Nat := 4983230072969 + 3 ^ 40 * 2236135 * 2
def baseEnd_2236135 : Nat := 1148212063341713845228709

theorem tailTrace_2236135 : CollatzResearch.WordTrace tailWord_2236135 prefixEnd_2236135 1148212063341713845228709 := by
  unfold tailWord_2236135
  simp only [CollatzResearch.WordTrace]
  refine ⟨81558543753872271298381859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54372362502581514198921239 81558543753872271298381859)
  ·
    refine ⟨122337815630808406947572789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81558543753872271298381859 122337815630808406947572789)
    ·
      refine ⟨11469170215388288151334949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122337815630808406947572789 11469170215388288151334949)
      ·
        refine ⟨2150469415385304028375303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11469170215388288151334949 2150469415385304028375303)
        ·
          refine ⟨3225704123077956042562955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2150469415385304028375303 3225704123077956042562955)
          ·
            refine ⟨4838556184616934063844433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3225704123077956042562955 4838556184616934063844433)
            ·
              refine ⟨3628917138462700547883325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838556184616934063844433 3628917138462700547883325)
              ·
                refine ⟨1360843926923512705456247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3628917138462700547883325 1360843926923512705456247)
                ·
                  refine ⟨2041265890385269058184371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360843926923512705456247 2041265890385269058184371)
                  ·
                    refine ⟨3061898835577903587276557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2041265890385269058184371 3061898835577903587276557)
                    ·
                      refine ⟨1148212063341713845228709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061898835577903587276557 1148212063341713845228709)
                      ·
                        rfl

theorem cell23_2236135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2236135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236135 prefixEnd_2236135 := by exact prefixLift 2236135
  have htrace : WordTrace (prefixWord ++ tailWord_2236135) baseStart_2236135 baseEnd_2236135 := by
    simpa [prefixWord, tailWord_2236135, baseEnd_2236135] using wordTrace_append hprefix tailTrace_2236135
  have hstable : (prefixWord ++ tailWord_2236135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236135).length < 2 ^ (prefixWord ++ tailWord_2236135).sum := by decide
  have hdescent : baseEnd_2236135 < baseStart_2236135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236141 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2236141 : Nat := 118140960795 + 2236141 * 2 ^ 59
def prefixEnd_2236141 : Nat := 4983230072969 + 3 ^ 40 * 2236141 * 2
def baseEnd_2236141 : Nat := 1148215144225640821753681

theorem tailTrace_2236141 : CollatzResearch.WordTrace tailWord_2236141 prefixEnd_2236141 1148215144225640821753681 := by
  unfold tailWord_2236141
  simp only [CollatzResearch.WordTrace]
  refine ⟨81558762591850534323100277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54372508394567022882066851 81558762591850534323100277)
  ·
    refine ⟨7646133992985987592790651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81558762591850534323100277 7646133992985987592790651)
    ·
      refine ⟨11469200989478981389185977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7646133992985987592790651 11469200989478981389185977)
      ·
        refine ⟨8601900742109236041889483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11469200989478981389185977 8601900742109236041889483)
        ·
          refine ⟨12902851113163854062834225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8601900742109236041889483 12902851113163854062834225)
          ·
            refine ⟨9677138334872890547125669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12902851113163854062834225 9677138334872890547125669)
            ·
              refine ⟨1814463437788666977586063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9677138334872890547125669 1814463437788666977586063)
              ·
                refine ⟨2721695156683000466379095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814463437788666977586063 2721695156683000466379095)
                ·
                  refine ⟨4082542735024500699568643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721695156683000466379095 4082542735024500699568643)
                  ·
                    refine ⟨6123814102536751049352965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4082542735024500699568643 6123814102536751049352965)
                    ·
                      refine ⟨1148215144225640821753681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6123814102536751049352965 1148215144225640821753681)
                      ·
                        rfl

theorem cell23_2236141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2236141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236141 prefixEnd_2236141 := by exact prefixLift 2236141
  have htrace : WordTrace (prefixWord ++ tailWord_2236141) baseStart_2236141 baseEnd_2236141 := by
    simpa [prefixWord, tailWord_2236141, baseEnd_2236141] using wordTrace_append hprefix tailTrace_2236141
  have hstable : (prefixWord ++ tailWord_2236141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236141).length < 2 ^ (prefixWord ++ tailWord_2236141).sum := by decide
  have hdescent : baseEnd_2236141 < baseStart_2236141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236174 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2236174 : Nat := 118140960795 + 2236174 * 2 ^ 59
def prefixEnd_2236174 : Nat := 4983230072969 + 3 ^ 40 * 2236174 * 2
def baseEnd_2236174 : Nat := 1148232089087239192641029

theorem tailTrace_2236174 : CollatzResearch.WordTrace tailWord_2236174 prefixEnd_2236174 1148232089087239192641029 := by
  unfold tailWord_2236174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10194995775091372619881447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54373310800487320639367717 10194995775091372619881447)
  ·
    refine ⟨15292493662637058929822171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10194995775091372619881447 15292493662637058929822171)
    ·
      refine ⟨22938740493955588394733257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15292493662637058929822171 22938740493955588394733257)
      ·
        refine ⟨17204055370466691296049943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22938740493955588394733257 17204055370466691296049943)
        ·
          refine ⟨25806083055700036944074915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17204055370466691296049943 25806083055700036944074915)
          ·
            refine ⟨38709124583550055416112373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25806083055700036944074915 38709124583550055416112373)
            ·
              refine ⟨3628980429707817695260535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38709124583550055416112373 3628980429707817695260535)
              ·
                refine ⟨5443470644561726542890803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628980429707817695260535 5443470644561726542890803)
                ·
                  refine ⟨8165205966842589814336205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5443470644561726542890803 8165205966842589814336205)
                  ·
                    refine ⟨3061952237565971180376077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8165205966842589814336205 3061952237565971180376077)
                    ·
                      refine ⟨1148232089087239192641029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061952237565971180376077 1148232089087239192641029)
                      ·
                        rfl

theorem cell23_2236174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2236174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236174 prefixEnd_2236174 := by exact prefixLift 2236174
  have htrace : WordTrace (prefixWord ++ tailWord_2236174) baseStart_2236174 baseEnd_2236174 := by
    simpa [prefixWord, tailWord_2236174, baseEnd_2236174] using wordTrace_append hprefix tailTrace_2236174
  have hstable : (prefixWord ++ tailWord_2236174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236174).length < 2 ^ (prefixWord ++ tailWord_2236174).sum := by decide
  have hdescent : baseEnd_2236174 < baseStart_2236174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236178 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2236178 : Nat := 118140960795 + 2236178 * 2 ^ 59
def prefixEnd_2236178 : Nat := 4983230072969 + 3 ^ 40 * 2236178 * 2
def baseEnd_2236178 : Nat := 1148234143009857176991011

theorem tailTrace_2236178 : CollatzResearch.WordTrace tailWord_2236178 prefixEnd_2236178 1148234143009857176991011 := by
  unfold tailWord_2236178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20390028023179122410549297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54373408061810993094798125 20390028023179122410549297)
  ·
    refine ⟨15292521017384341807911973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20390028023179122410549297 15292521017384341807911973)
    ·
      refine ⟨2867347690759564088983495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15292521017384341807911973 2867347690759564088983495)
      ·
        refine ⟨4301021536139346133475243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2867347690759564088983495 4301021536139346133475243)
        ·
          refine ⟨6451532304209019200212865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4301021536139346133475243 6451532304209019200212865)
          ·
            refine ⟨4838649228156764400159649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6451532304209019200212865 4838649228156764400159649)
            ·
              refine ⟨3628986921117573300119737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838649228156764400159649 3628986921117573300119737)
              ·
                refine ⟨2721740190838179975089803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628986921117573300119737 2721740190838179975089803)
                ·
                  refine ⟨4082610286257269962634705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721740190838179975089803 4082610286257269962634705)
                  ·
                    refine ⟨3061957714692952471976029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4082610286257269962634705 3061957714692952471976029)
                    ·
                      refine ⟨1148234143009857176991011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3061957714692952471976029 1148234143009857176991011)
                      ·
                        rfl

theorem cell23_2236178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2236178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236178 prefixEnd_2236178 := by exact prefixLift 2236178
  have htrace : WordTrace (prefixWord ++ tailWord_2236178) baseStart_2236178 baseEnd_2236178 := by
    simpa [prefixWord, tailWord_2236178, baseEnd_2236178] using wordTrace_append hprefix tailTrace_2236178
  have hstable : (prefixWord ++ tailWord_2236178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236178).length < 2 ^ (prefixWord ++ tailWord_2236178).sum := by decide
  have hdescent : baseEnd_2236178 < baseStart_2236178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236184 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 3, 3, 2]
def baseStart_2236184 : Nat := 118140960795 + 2236184 * 2 ^ 59
def prefixEnd_2236184 : Nat := 4983230072969 + 3 ^ 40 * 2236184 * 2
def baseEnd_2236184 : Nat := 1148237223893784153515983

theorem tailTrace_2236184 : CollatzResearch.WordTrace tailWord_2236184 prefixEnd_2236184 1148237223893784153515983 := by
  unfold tailWord_2236184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40780165465347376333457803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54373553953796501777943737 40780165465347376333457803)
  ·
    refine ⟨61170248198021064500186705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40780165465347376333457803 61170248198021064500186705)
    ·
      refine ⟨45877686148515798375140029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61170248198021064500186705 45877686148515798375140029)
      ·
        refine ⟨17204132305693424390677511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45877686148515798375140029 17204132305693424390677511)
        ·
          refine ⟨25806198458540136586016267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17204132305693424390677511 25806198458540136586016267)
          ·
            refine ⟨38709297687810204879024401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25806198458540136586016267 38709297687810204879024401)
            ·
              refine ⟨29031973265857653659268301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38709297687810204879024401 29031973265857653659268301)
              ·
                refine ⟨10886989974696620122225613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29031973265857653659268301 10886989974696620122225613)
                ·
                  refine ⟨4082621240511232545834605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10886989974696620122225613 4082621240511232545834605)
                  ·
                    refine ⟨1530982965191712204687977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4082621240511232545834605 1530982965191712204687977)
                    ·
                      refine ⟨1148237223893784153515983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1530982965191712204687977 1148237223893784153515983)
                      ·
                        rfl

theorem cell23_2236184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_2236184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236184 prefixEnd_2236184 := by exact prefixLift 2236184
  have htrace : WordTrace (prefixWord ++ tailWord_2236184) baseStart_2236184 baseEnd_2236184 := by
    simpa [prefixWord, tailWord_2236184, baseEnd_2236184] using wordTrace_append hprefix tailTrace_2236184
  have hstable : (prefixWord ++ tailWord_2236184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236184).length < 2 ^ (prefixWord ++ tailWord_2236184).sum := by decide
  have hdescent : baseEnd_2236184 < baseStart_2236184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236264 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2236264 : Nat := 118140960795 + 2236264 * 2 ^ 59
def prefixEnd_2236264 : Nat := 4983230072969 + 3 ^ 40 * 2236264 * 2
def baseEnd_2236264 : Nat := 1148278302346143840515615

theorem tailTrace_2236264 : CollatzResearch.WordTrace tailWord_2236264 prefixEnd_2236264 1148278302346143840515615 := by
  unfold tailWord_2236264
  simp only [CollatzResearch.WordTrace]
  refine ⟨40781624385202463164913923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54375499180269950886551897 40781624385202463164913923)
  ·
    refine ⟨61172436577803694747370885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40781624385202463164913923 61172436577803694747370885)
    ·
      refine ⟨11469831858338192765132041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61172436577803694747370885 11469831858338192765132041)
      ·
        refine ⟨8602373893753644573849031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11469831858338192765132041 8602373893753644573849031)
        ·
          refine ⟨12903560840630466860773547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8602373893753644573849031 12903560840630466860773547)
          ·
            refine ⟨19355341260945700291160321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12903560840630466860773547 19355341260945700291160321)
            ·
              refine ⟨14516505945709275218370241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19355341260945700291160321 14516505945709275218370241)
              ·
                refine ⟨10887379459281956413777681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14516505945709275218370241 10887379459281956413777681)
                ·
                  refine ⟨8165534594461467310333261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10887379459281956413777681 8165534594461467310333261)
                  ·
                    refine ⟨3062075472923050241374973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8165534594461467310333261 3062075472923050241374973)
                    ·
                      refine ⟨1148278302346143840515615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062075472923050241374973 1148278302346143840515615)
                      ·
                        rfl

theorem cell23_2236264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2236264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236264 prefixEnd_2236264 := by exact prefixLift 2236264
  have htrace : WordTrace (prefixWord ++ tailWord_2236264) baseStart_2236264 baseEnd_2236264 := by
    simpa [prefixWord, tailWord_2236264, baseEnd_2236264] using wordTrace_append hprefix tailTrace_2236264
  have hstable : (prefixWord ++ tailWord_2236264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236264).length < 2 ^ (prefixWord ++ tailWord_2236264).sum := by decide
  have hdescent : baseEnd_2236264 < baseStart_2236264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236287 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_2236287 : Nat := 118140960795 + 2236287 * 2 ^ 59
def prefixEnd_2236287 : Nat := 4983230072969 + 3 ^ 40 * 2236287 * 2
def baseEnd_2236287 : Nat := 1148290112401197250528009

theorem tailTrace_2236287 : CollatzResearch.WordTrace tailWord_2236287 prefixEnd_2236287 1148290112401197250528009 := by
  unfold tailWord_2236287
  simp only [CollatzResearch.WordTrace]
  refine ⟨81564087649321601257915115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54376058432881067505276743 81564087649321601257915115)
  ·
    refine ⟨122346131473982401886872673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81564087649321601257915115 122346131473982401886872673)
    ·
      refine ⟨91759598605486801415154505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122346131473982401886872673 91759598605486801415154505)
      ·
        refine ⟨68819698954115101061365879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91759598605486801415154505 68819698954115101061365879)
        ·
          refine ⟨103229548431172651592048819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68819698954115101061365879 103229548431172651592048819)
          ·
            refine ⟨154844322646758977388073229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103229548431172651592048819 154844322646758977388073229)
            ·
              refine ⟨58066620992534616520527461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154844322646758977388073229 58066620992534616520527461)
              ·
                refine ⟨10887491436100240597598899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58066620992534616520527461 10887491436100240597598899)
                ·
                  refine ⟨16331237154150360896398349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10887491436100240597598899 16331237154150360896398349)
                  ·
                    refine ⟨6124213932806385336149381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16331237154150360896398349 6124213932806385336149381)
                    ·
                      refine ⟨1148290112401197250528009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6124213932806385336149381 1148290112401197250528009)
                      ·
                        rfl

theorem cell23_2236287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_2236287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236287 prefixEnd_2236287 := by exact prefixLift 2236287
  have htrace : WordTrace (prefixWord ++ tailWord_2236287) baseStart_2236287 baseEnd_2236287 := by
    simpa [prefixWord, tailWord_2236287, baseEnd_2236287] using wordTrace_append hprefix tailTrace_2236287
  have hstable : (prefixWord ++ tailWord_2236287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236287).length < 2 ^ (prefixWord ++ tailWord_2236287).sum := by decide
  have hdescent : baseEnd_2236287 < baseStart_2236287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236304 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 4, 4, 2]
def baseStart_2236304 : Nat := 118140960795 + 2236304 * 2 ^ 59
def prefixEnd_2236304 : Nat := 4983230072969 + 3 ^ 40 * 2236304 * 2
def baseEnd_2236304 : Nat := 1148298841572323684015431

theorem tailTrace_2236304 : CollatzResearch.WordTrace tailWord_2236304 prefixEnd_2236304 1148298841572323684015431 := by
  unfold tailWord_2236304
  simp only [CollatzResearch.WordTrace]
  refine ⟨40782353845130006580641983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54376471793506675440855977 40782353845130006580641983)
  ·
    refine ⟨61173530767695009870962975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40782353845130006580641983 61173530767695009870962975)
    ·
      refine ⟨91760296151542514806444463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61173530767695009870962975 91760296151542514806444463)
      ·
        refine ⟨137640444227313772209666695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91760296151542514806444463 137640444227313772209666695)
        ·
          refine ⟨206460666340970658314500043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137640444227313772209666695 206460666340970658314500043)
          ·
            refine ⟨309690999511455987471750065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206460666340970658314500043 309690999511455987471750065)
            ·
              refine ⟨232268249633591990603812549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309690999511455987471750065 232268249633591990603812549)
              ·
                refine ⟨43550296806298498238214853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232268249633591990603812549 43550296806298498238214853)
                ·
                  refine ⟨8165680651180968419665285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43550296806298498238214853 8165680651180968419665285)
                  ·
                    refine ⟨1531065122096431578687241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8165680651180968419665285 1531065122096431578687241)
                    ·
                      refine ⟨1148298841572323684015431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531065122096431578687241 1148298841572323684015431)
                      ·
                        rfl

theorem cell23_2236304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 4, 2].length) (baseStart_2236304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236304 prefixEnd_2236304 := by exact prefixLift 2236304
  have htrace : WordTrace (prefixWord ++ tailWord_2236304) baseStart_2236304 baseEnd_2236304 := by
    simpa [prefixWord, tailWord_2236304, baseEnd_2236304] using wordTrace_append hprefix tailTrace_2236304
  have hstable : (prefixWord ++ tailWord_2236304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236304).length < 2 ^ (prefixWord ++ tailWord_2236304).sum := by decide
  have hdescent : baseEnd_2236304 < baseStart_2236304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236411 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 4]
def baseStart_2236411 : Nat := 118140960795 + 2236411 * 2 ^ 59
def prefixEnd_2236411 : Nat := 4983230072969 + 3 ^ 40 * 2236411 * 2
def baseEnd_2236411 : Nat := 1148353784002354765377439

theorem tailTrace_2236411 : CollatzResearch.WordTrace tailWord_2236411 prefixEnd_2236411 1148353784002354765377439 := by
  unfold tailWord_2236411
  simp only [CollatzResearch.WordTrace]
  refine ⟨81568610300872370435429087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54379073533914913623619391 81568610300872370435429087)
  ·
    refine ⟨122352915451308555653143631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81568610300872370435429087 122352915451308555653143631)
    ·
      refine ⟨183529373176962833479715447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122352915451308555653143631 183529373176962833479715447)
      ·
        refine ⟨275294059765444250219573171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183529373176962833479715447 275294059765444250219573171)
        ·
          refine ⟨412941089648166375329359757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275294059765444250219573171 412941089648166375329359757)
          ·
            refine ⟨154852908618062390748509909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 412941089648166375329359757 154852908618062390748509909)
            ·
              refine ⟨3629365045735837283168201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 154852908618062390748509909 3629365045735837283168201)
              ·
                refine ⟨2722023784301877962376151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629365045735837283168201 2722023784301877962376151)
                ·
                  refine ⟨4083035676452816943564227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722023784301877962376151 4083035676452816943564227)
                  ·
                    refine ⟨6124553514679225415346341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083035676452816943564227 6124553514679225415346341)
                    ·
                      refine ⟨1148353784002354765377439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6124553514679225415346341 1148353784002354765377439)
                      ·
                        rfl

theorem cell23_2236411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 4].length) (baseStart_2236411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236411 prefixEnd_2236411 := by exact prefixLift 2236411
  have htrace : WordTrace (prefixWord ++ tailWord_2236411) baseStart_2236411 baseEnd_2236411 := by
    simpa [prefixWord, tailWord_2236411, baseEnd_2236411] using wordTrace_append hprefix tailTrace_2236411
  have hstable : (prefixWord ++ tailWord_2236411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236411).length < 2 ^ (prefixWord ++ tailWord_2236411).sum := by decide
  have hdescent : baseEnd_2236411 < baseStart_2236411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236428 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 1, 1, 4]
def baseStart_2236428 : Nat := 118140960795 + 2236428 * 2 ^ 59
def prefixEnd_2236428 : Nat := 4983230072969 + 3 ^ 40 * 2236428 * 2
def baseEnd_2236428 : Nat := 1148362513173481198864861

theorem tailTrace_2236428 : CollatzResearch.WordTrace tailWord_2236428 prefixEnd_2236428 1148362513173481198864861 := by
  unfold tailWord_2236428
  simp only [CollatzResearch.WordTrace]
  refine ⟨40784615170905391169398969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54379486894540521559198625 40784615170905391169398969)
  ·
    refine ⟨30588461378179043377049227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40784615170905391169398969 30588461378179043377049227)
    ·
      refine ⟨45882692067268565065573841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30588461378179043377049227 45882692067268565065573841)
      ·
        refine ⟨34412019050451423799180381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45882692067268565065573841 34412019050451423799180381)
        ·
          refine ⟨12904507143919283924692643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34412019050451423799180381 12904507143919283924692643)
          ·
            refine ⟨19356760715878925887038965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12904507143919283924692643 19356760715878925887038965)
            ·
              refine ⟨1814696317113649301909903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19356760715878925887038965 1814696317113649301909903)
              ·
                refine ⟨2722044475670473952864855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814696317113649301909903 2722044475670473952864855)
                ·
                  refine ⟨4083066713505710929297283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722044475670473952864855 4083066713505710929297283)
                  ·
                    refine ⟨6124600070258566393945925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083066713505710929297283 6124600070258566393945925)
                    ·
                      refine ⟨1148362513173481198864861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6124600070258566393945925 1148362513173481198864861)
                      ·
                        rfl

theorem cell23_2236428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_2236428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236428 prefixEnd_2236428 := by exact prefixLift 2236428
  have htrace : WordTrace (prefixWord ++ tailWord_2236428) baseStart_2236428 baseEnd_2236428 := by
    simpa [prefixWord, tailWord_2236428, baseEnd_2236428] using wordTrace_append hprefix tailTrace_2236428
  have hstable : (prefixWord ++ tailWord_2236428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236428).length < 2 ^ (prefixWord ++ tailWord_2236428).sum := by decide
  have hdescent : baseEnd_2236428 < baseStart_2236428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236439 : List Nat := [1, 1, 3, 5, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2236439 : Nat := 118140960795 + 2236439 * 2 ^ 59
def prefixEnd_2236439 : Nat := 4983230072969 + 3 ^ 40 * 2236439 * 2
def baseEnd_2236439 : Nat := 1148368161460680655827311

theorem tailTrace_2236439 : CollatzResearch.WordTrace tailWord_2236439 prefixEnd_2236439 1148368161460680655827311 := by
  unfold tailWord_2236439
  simp only [CollatzResearch.WordTrace]
  refine ⟨81569631544770931217448371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54379754363180620811632247 81569631544770931217448371)
  ·
    refine ⟨122354447317156396826172557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81569631544770931217448371 122354447317156396826172557)
    ·
      refine ⟨45882917743933648809814709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122354447317156396826172557 45882917743933648809814709)
      ·
        refine ⟨4301523538493779575920129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45882917743933648809814709 4301523538493779575920129)
        ·
          refine ⟨3226142653870334681940097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4301523538493779575920129 3226142653870334681940097)
          ·
            refine ⟨2419606990402751011455073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3226142653870334681940097 2419606990402751011455073)
            ·
              refine ⟨1814705242802063258591305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419606990402751011455073 1814705242802063258591305)
              ·
                refine ⟨1361028932101547443943479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814705242802063258591305 1361028932101547443943479)
                ·
                  refine ⟨2041543398152321165915219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361028932101547443943479 2041543398152321165915219)
                  ·
                    refine ⟨3062315097228481748872829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2041543398152321165915219 3062315097228481748872829)
                    ·
                      refine ⟨1148368161460680655827311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062315097228481748872829 1148368161460680655827311)
                      ·
                        rfl

theorem cell23_2236439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2236439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236439 prefixEnd_2236439 := by exact prefixLift 2236439
  have htrace : WordTrace (prefixWord ++ tailWord_2236439) baseStart_2236439 baseEnd_2236439 := by
    simpa [prefixWord, tailWord_2236439, baseEnd_2236439] using wordTrace_append hprefix tailTrace_2236439
  have hstable : (prefixWord ++ tailWord_2236439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236439).length < 2 ^ (prefixWord ++ tailWord_2236439).sum := by decide
  have hdescent : baseEnd_2236439 < baseStart_2236439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236458 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2236458 : Nat := 118140960795 + 2236458 * 2 ^ 59
def prefixEnd_2236458 : Nat := 4983230072969 + 3 ^ 40 * 2236458 * 2
def baseEnd_2236458 : Nat := 1148377917593116081489723

theorem tailTrace_2236458 : CollatzResearch.WordTrace tailWord_2236458 prefixEnd_2236458 1148377917593116081489723 := by
  unfold tailWord_2236458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20392581132925524365597507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54380216354468064974926685 20392581132925524365597507)
  ·
    refine ⟨30588871699388286548396261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20392581132925524365597507 30588871699388286548396261)
    ·
      refine ⟨5735413443635303727824299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30588871699388286548396261 5735413443635303727824299)
      ·
        refine ⟨8603120165452955591736449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5735413443635303727824299 8603120165452955591736449)
        ·
          refine ⟨6452340124089716693802337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8603120165452955591736449 6452340124089716693802337)
          ·
            refine ⟨4839255093067287520351753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6452340124089716693802337 4839255093067287520351753)
            ·
              refine ⟨3629441319800465640263815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4839255093067287520351753 3629441319800465640263815)
              ·
                refine ⟨5444161979700698460395723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3629441319800465640263815 5444161979700698460395723)
                ·
                  refine ⟨8166242969551047690593585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5444161979700698460395723 8166242969551047690593585)
                  ·
                    refine ⟨6124682227163285767945189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8166242969551047690593585 6124682227163285767945189)
                    ·
                      refine ⟨1148377917593116081489723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6124682227163285767945189 1148377917593116081489723)
                      ·
                        rfl

theorem cell23_2236458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2236458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236458 prefixEnd_2236458 := by exact prefixLift 2236458
  have htrace : WordTrace (prefixWord ++ tailWord_2236458) baseStart_2236458 baseEnd_2236458 := by
    simpa [prefixWord, tailWord_2236458, baseEnd_2236458] using wordTrace_append hprefix tailTrace_2236458
  have hstable : (prefixWord ++ tailWord_2236458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236458).length < 2 ^ (prefixWord ++ tailWord_2236458).sum := by decide
  have hdescent : baseEnd_2236458 < baseStart_2236458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236474 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_2236474 : Nat := 118140960795 + 2236474 * 2 ^ 59
def prefixEnd_2236474 : Nat := 4983230072969 + 3 ^ 40 * 2236474 * 2
def baseEnd_2236474 : Nat := 1148386133283588018889649

theorem tailTrace_2236474 : CollatzResearch.WordTrace tailWord_2236474 prefixEnd_2236474 1148386133283588018889649 := by
  unfold tailWord_2236474
  simp only [CollatzResearch.WordTrace]
  refine ⟨20392727024911033048743119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54380605399762754796648317 20392727024911033048743119)
  ·
    refine ⟨30589090537366549573114679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20392727024911033048743119 30589090537366549573114679)
    ·
      refine ⟨45883635806049824359672019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30589090537366549573114679 45883635806049824359672019)
      ·
        refine ⟨68825453709074736539508029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45883635806049824359672019 68825453709074736539508029)
        ·
          refine ⟨25809545140903026202315511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68825453709074736539508029 25809545140903026202315511)
          ·
            refine ⟨38714317711354539303473267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25809545140903026202315511 38714317711354539303473267)
            ·
              refine ⟨58071476567031808955209901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38714317711354539303473267 58071476567031808955209901)
              ·
                refine ⟨21776803712636928358203713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58071476567031808955209901 21776803712636928358203713)
                ·
                  refine ⟨16332602784477696268652785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21776803712636928358203713 16332602784477696268652785)
                  ·
                    refine ⟨12249452088358272201489589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16332602784477696268652785 12249452088358272201489589)
                    ·
                      refine ⟨1148386133283588018889649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12249452088358272201489589 1148386133283588018889649)
                      ·
                        rfl

theorem cell23_2236474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_2236474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236474 prefixEnd_2236474 := by exact prefixLift 2236474
  have htrace : WordTrace (prefixWord ++ tailWord_2236474) baseStart_2236474 baseEnd_2236474 := by
    simpa [prefixWord, tailWord_2236474, baseEnd_2236474] using wordTrace_append hprefix tailTrace_2236474
  have hstable : (prefixWord ++ tailWord_2236474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236474).length < 2 ^ (prefixWord ++ tailWord_2236474).sum := by decide
  have hdescent : baseEnd_2236474 < baseStart_2236474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236522 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_2236522 : Nat := 118140960795 + 2236522 * 2 ^ 59
def prefixEnd_2236522 : Nat := 4983230072969 + 3 ^ 40 * 2236522 * 2
def baseEnd_2236522 : Nat := 1148410780355003831089429

theorem tailTrace_2236522 : CollatzResearch.WordTrace tailWord_2236522 prefixEnd_2236522 1148410780355003831089429 := by
  unfold tailWord_2236522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20393164700867559098179955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54381772535646824261813213 20393164700867559098179955)
  ·
    refine ⟨30589747051301338647269933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20393164700867559098179955 30589747051301338647269933)
    ·
      refine ⟨11471155144238001992726225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30589747051301338647269933 11471155144238001992726225)
      ·
        refine ⟨8603366358178501494544669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11471155144238001992726225 8603366358178501494544669)
        ·
          refine ⟨3226262384316938060454251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8603366358178501494544669 3226262384316938060454251)
          ·
            refine ⟨4839393576475407090681377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226262384316938060454251 4839393576475407090681377)
            ·
              refine ⟨3629545182356555318011033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4839393576475407090681377 3629545182356555318011033)
              ·
                refine ⟨2722158886767416488508275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629545182356555318011033 2722158886767416488508275)
                ·
                  refine ⟨4083238330151124732762413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722158886767416488508275 4083238330151124732762413)
                  ·
                    refine ⟨1531214373806671774785905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4083238330151124732762413 1531214373806671774785905)
                    ·
                      refine ⟨1148410780355003831089429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531214373806671774785905 1148410780355003831089429)
                      ·
                        rfl

theorem cell23_2236522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_2236522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236522 prefixEnd_2236522 := by exact prefixLift 2236522
  have htrace : WordTrace (prefixWord ++ tailWord_2236522) baseStart_2236522 baseEnd_2236522 := by
    simpa [prefixWord, tailWord_2236522, baseEnd_2236522] using wordTrace_append hprefix tailTrace_2236522
  have hstable : (prefixWord ++ tailWord_2236522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236522).length < 2 ^ (prefixWord ++ tailWord_2236522).sum := by decide
  have hdescent : baseEnd_2236522 < baseStart_2236522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236551 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_2236551 : Nat := 118140960795 + 2236551 * 2 ^ 59
def prefixEnd_2236551 : Nat := 4983230072969 + 3 ^ 40 * 2236551 * 2
def baseEnd_2236551 : Nat := 1148425671293984217626795

theorem tailTrace_2236551 : CollatzResearch.WordTrace tailWord_2236551 prefixEnd_2236551 1148425671293984217626795 := by
  unfold tailWord_2236551
  simp only [CollatzResearch.WordTrace]
  refine ⟨81573716520365174345525507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54382477680243449563683671 81573716520365174345525507)
  ·
    refine ⟨122360574780547761518288261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81573716520365174345525507 122360574780547761518288261)
    ·
      refine ⟨22942607771352705284679049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122360574780547761518288261 22942607771352705284679049)
      ·
        refine ⟨17206955828514528963509287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22942607771352705284679049 17206955828514528963509287)
        ·
          refine ⟨25810433742771793445263931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17206955828514528963509287 25810433742771793445263931)
          ·
            refine ⟨38715650614157690167895897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25810433742771793445263931 38715650614157690167895897)
            ·
              refine ⟨29036737960618267625921923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38715650614157690167895897 29036737960618267625921923)
              ·
                refine ⟨43555106940927401438882885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29036737960618267625921923 43555106940927401438882885)
                ·
                  refine ⟨8166582551423887769790541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43555106940927401438882885 8166582551423887769790541)
                  ·
                    refine ⟨3062468456783957913671453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8166582551423887769790541 3062468456783957913671453)
                    ·
                      refine ⟨1148425671293984217626795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062468456783957913671453 1148425671293984217626795)
                      ·
                        rfl

theorem cell23_2236551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_2236551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236551 prefixEnd_2236551 := by exact prefixLift 2236551
  have htrace : WordTrace (prefixWord ++ tailWord_2236551) baseStart_2236551 baseEnd_2236551 := by
    simpa [prefixWord, tailWord_2236551, baseEnd_2236551] using wordTrace_append hprefix tailTrace_2236551
  have hstable : (prefixWord ++ tailWord_2236551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236551).length < 2 ^ (prefixWord ++ tailWord_2236551).sum := by decide
  have hdescent : baseEnd_2236551 < baseStart_2236551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236608 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_2236608 : Nat := 118140960795 + 2236608 * 2 ^ 59
def prefixEnd_2236608 : Nat := 4983230072969 + 3 ^ 40 * 2236608 * 2
def baseEnd_2236608 : Nat := 1148454939691290494614033

theorem tailTrace_2236608 : CollatzResearch.WordTrace tailWord_2236608 prefixEnd_2236608 1148454939691290494614033 := by
  unfold tailWord_2236608
  simp only [CollatzResearch.WordTrace]
  refine ⟨40787897740579336540175239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54383863654105782053566985 40787897740579336540175239)
  ·
    refine ⟨61181846610869004810262859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40787897740579336540175239 61181846610869004810262859)
    ·
      refine ⟨91772769916303507215394289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61181846610869004810262859 91772769916303507215394289)
      ·
        refine ⟨68829577437227630411545717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91772769916303507215394289 68829577437227630411545717)
        ·
          refine ⟨6452772884740090351082411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68829577437227630411545717 6452772884740090351082411)
          ·
            refine ⟨9679159327110135526623617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6452772884740090351082411 9679159327110135526623617)
            ·
              refine ⟨7259369495332601644967713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9679159327110135526623617 7259369495332601644967713)
              ·
                refine ⟨5444527121499451233725785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7259369495332601644967713 5444527121499451233725785)
                ·
                  refine ⟨4083395341124588425294339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5444527121499451233725785 4083395341124588425294339)
                  ·
                    refine ⟨6125093011686882637941509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083395341124588425294339 6125093011686882637941509)
                    ·
                      refine ⟨1148454939691290494614033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6125093011686882637941509 1148454939691290494614033)
                      ·
                        rfl

theorem cell23_2236608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_2236608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236608 prefixEnd_2236608 := by exact prefixLift 2236608
  have htrace : WordTrace (prefixWord ++ tailWord_2236608) baseStart_2236608 baseEnd_2236608 := by
    simpa [prefixWord, tailWord_2236608, baseEnd_2236608] using wordTrace_append hprefix tailTrace_2236608
  have hstable : (prefixWord ++ tailWord_2236608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236608).length < 2 ^ (prefixWord ++ tailWord_2236608).sum := by decide
  have hdescent : baseEnd_2236608 < baseStart_2236608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236609 : List Nat := [1, 2, 6, 1, 2, 2, 2, 2, 5]
def baseStart_2236609 : Nat := 118140960795 + 2236609 * 2 ^ 59
def prefixEnd_2236609 : Nat := 4983230072969 + 3 ^ 40 * 2236609 * 2
def baseEnd_2236609 : Nat := 127606161463549443411281

theorem tailTrace_2236609 : CollatzResearch.WordTrace tailWord_2236609 prefixEnd_2236609 127606161463549443411281 := by
  unfold tailWord_2236609
  simp only [CollatzResearch.WordTrace]
  refine ⟨81575831954155050251136881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54383887969436700167424587 81575831954155050251136881)
  ·
    refine ⟨61181873965616287688352661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81575831954155050251136881 61181873965616287688352661)
    ·
      refine ⟨2867900342138263485391531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61181873965616287688352661 2867900342138263485391531)
      ·
        refine ⟨4301850513207395228087297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2867900342138263485391531 4301850513207395228087297)
        ·
          refine ⟨3226387884905546421065473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4301850513207395228087297 3226387884905546421065473)
          ·
            refine ⟨2419790913679159815799105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3226387884905546421065473 2419790913679159815799105)
            ·
              refine ⟨1814843185259369861849329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419790913679159815799105 1814843185259369861849329)
              ·
                refine ⟨1361132388944527396386997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814843185259369861849329 1361132388944527396386997)
                ·
                  refine ⟨127606161463549443411281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1361132388944527396386997 127606161463549443411281)
                  ·
                    rfl

theorem cell23_2236609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 5].length) (baseStart_2236609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236609 prefixEnd_2236609 := by exact prefixLift 2236609
  have htrace : WordTrace (prefixWord ++ tailWord_2236609) baseStart_2236609 baseEnd_2236609 := by
    simpa [prefixWord, tailWord_2236609, baseEnd_2236609] using wordTrace_append hprefix tailTrace_2236609
  have hstable : (prefixWord ++ tailWord_2236609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236609).length < 2 ^ (prefixWord ++ tailWord_2236609).sum := by decide
  have hdescent : baseEnd_2236609 < baseStart_2236609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236618 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_2236618 : Nat := 118140960795 + 2236618 * 2 ^ 59
def prefixEnd_2236618 : Nat := 4983230072969 + 3 ^ 40 * 2236618 * 2
def baseEnd_2236618 : Nat := 382820024832611818496329

theorem tailTrace_2236618 : CollatzResearch.WordTrace tailWord_2236618 prefixEnd_2236618 382820024832611818496329 := by
  unfold tailWord_2236618
  simp only [CollatzResearch.WordTrace]
  refine ⟨20394040052780611197053627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54384106807414963192143005 20394040052780611197053627)
  ·
    refine ⟨30591060079170916795580441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20394040052780611197053627 30591060079170916795580441)
    ·
      refine ⟨22943295059378187596685331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30591060079170916795580441 22943295059378187596685331)
      ·
        refine ⟨34414942589067281395027997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22943295059378187596685331 34414942589067281395027997)
        ·
          refine ⟨12905603470900230523135499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34414942589067281395027997 12905603470900230523135499)
          ·
            refine ⟨19358405206350345784703249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12905603470900230523135499 19358405206350345784703249)
            ·
              refine ⟨14518803904762759338527437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19358405206350345784703249 14518803904762759338527437)
              ·
                refine ⟨5444551464286034751947789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14518803904762759338527437 5444551464286034751947789)
                ·
                  refine ⟨2041706799107263031980421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5444551464286034751947789 2041706799107263031980421)
                  ·
                    refine ⟨382820024832611818496329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2041706799107263031980421 382820024832611818496329)
                    ·
                      rfl

theorem cell23_2236618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_2236618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236618 prefixEnd_2236618 := by exact prefixLift 2236618
  have htrace : WordTrace (prefixWord ++ tailWord_2236618) baseStart_2236618 baseEnd_2236618 := by
    simpa [prefixWord, tailWord_2236618, baseEnd_2236618] using wordTrace_append hprefix tailTrace_2236618
  have hstable : (prefixWord ++ tailWord_2236618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236618).length < 2 ^ (prefixWord ++ tailWord_2236618).sum := by decide
  have hdescent : baseEnd_2236618 < baseStart_2236618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236645 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2236645 : Nat := 118140960795 + 2236645 * 2 ^ 59
def prefixEnd_2236645 : Nat := 4983230072969 + 3 ^ 40 * 2236645 * 2
def baseEnd_2236645 : Nat := 1148473938475506849851363

theorem tailTrace_2236645 : CollatzResearch.WordTrace tailWord_2236645 prefixEnd_2236645 1148473938475506849851363 := by
  unfold tailWord_2236645
  simp only [CollatzResearch.WordTrace]
  refine ⟨81577144982024628399447389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54384763321349752266298259 81577144982024628399447389)
  ·
    refine ⟨30591429368259235649792771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81577144982024628399447389 30591429368259235649792771)
    ·
      refine ⟨45887144052388853474689157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30591429368259235649792771 45887144052388853474689157)
      ·
        refine ⟨8603839509822910026504217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45887144052388853474689157 8603839509822910026504217)
        ·
          refine ⟨6452879632367182519878163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8603839509822910026504217 6452879632367182519878163)
          ·
            refine ⟨9679319448550773779817245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6452879632367182519878163 9679319448550773779817245)
            ·
              refine ⟨3629744793206540167431467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9679319448550773779817245 3629744793206540167431467)
              ·
                refine ⟨5444617189809810251147201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3629744793206540167431467 5444617189809810251147201)
                ·
                  refine ⟨4083462892357357688360401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5444617189809810251147201 4083462892357357688360401)
                  ·
                    refine ⟨3062597169268018266270301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4083462892357357688360401 3062597169268018266270301)
                    ·
                      refine ⟨1148473938475506849851363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062597169268018266270301 1148473938475506849851363)
                      ·
                        rfl

theorem cell23_2236645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2236645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236645 prefixEnd_2236645 := by exact prefixLift 2236645
  have htrace : WordTrace (prefixWord ++ tailWord_2236645) baseStart_2236645 baseEnd_2236645 := by
    simpa [prefixWord, tailWord_2236645, baseEnd_2236645] using wordTrace_append hprefix tailTrace_2236645
  have hstable : (prefixWord ++ tailWord_2236645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236645).length < 2 ^ (prefixWord ++ tailWord_2236645).sum := by decide
  have hdescent : baseEnd_2236645 < baseStart_2236645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236675 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 3]
def baseStart_2236675 : Nat := 118140960795 + 2236675 * 2 ^ 59
def prefixEnd_2236675 : Nat := 4983230072969 + 3 ^ 40 * 2236675 * 2
def baseEnd_2236675 : Nat := 1148489342895141732476225

theorem tailTrace_2236675 : CollatzResearch.WordTrace tailWord_2236675 prefixEnd_2236675 1148489342895141732476225 := by
  unfold tailWord_2236675
  simp only [CollatzResearch.WordTrace]
  refine ⟨81578239171915943523039479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54385492781277295682026319 81578239171915943523039479)
  ·
    refine ⟨122367358757873915284559219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81578239171915943523039479 122367358757873915284559219)
    ·
      refine ⟨183551038136810872926838829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122367358757873915284559219 183551038136810872926838829)
      ·
        refine ⟨68831639301304077347564561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183551038136810872926838829 68831639301304077347564561)
        ·
          refine ⟨51623729475978058010673421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68831639301304077347564561 51623729475978058010673421)
          ·
            refine ⟨19358898553491771754002533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51623729475978058010673421 19358898553491771754002533)
            ·
              refine ⟨3629793478779707203875475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19358898553491771754002533 3629793478779707203875475)
              ·
                refine ⟨5444690218169560805813213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3629793478779707203875475 5444690218169560805813213)
                ·
                  refine ⟨2041758831813585302179955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5444690218169560805813213 2041758831813585302179955)
                  ·
                    refine ⟨3062638247720377953269933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2041758831813585302179955 3062638247720377953269933)
                    ·
                      refine ⟨1148489342895141732476225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062638247720377953269933 1148489342895141732476225)
                      ·
                        rfl

theorem cell23_2236675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_2236675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236675 prefixEnd_2236675 := by exact prefixLift 2236675
  have htrace : WordTrace (prefixWord ++ tailWord_2236675) baseStart_2236675 baseEnd_2236675 := by
    simpa [prefixWord, tailWord_2236675, baseEnd_2236675] using wordTrace_append hprefix tailTrace_2236675
  have hstable : (prefixWord ++ tailWord_2236675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236675).length < 2 ^ (prefixWord ++ tailWord_2236675).sum := by decide
  have hdescent : baseEnd_2236675 < baseStart_2236675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236695 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 1, 5]
def baseStart_2236695 : Nat := 118140960795 + 2236695 * 2 ^ 59
def prefixEnd_2236695 : Nat := 4983230072969 + 3 ^ 40 * 2236695 * 2
def baseEnd_2236695 : Nat := 382833204169410551408711

theorem tailTrace_2236695 : CollatzResearch.WordTrace tailWord_2236695 prefixEnd_2236695 382833204169410551408711 := by
  unfold tailWord_2236695
  simp only [CollatzResearch.WordTrace]
  refine ⟨81578968631843486938767539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54385979087895657959178359 81578968631843486938767539)
  ·
    refine ⟨122368452947765230408151309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81578968631843486938767539 122368452947765230408151309)
    ·
      refine ⟨45888169855411961403056741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122368452947765230408151309 45888169855411961403056741)
      ·
        refine ⟨8604031847889742763073139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45888169855411961403056741 8604031847889742763073139)
        ·
          refine ⟨12906047771834614144609709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604031847889742763073139 12906047771834614144609709)
          ·
            refine ⟨4839767914437980304228641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12906047771834614144609709 4839767914437980304228641)
            ·
              refine ⟨3629825935828485228171481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4839767914437980304228641 3629825935828485228171481)
              ·
                refine ⟨2722369451871363921128611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629825935828485228171481 2722369451871363921128611)
                ·
                  refine ⟨4083554177807045881692917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722369451871363921128611 4083554177807045881692917)
                  ·
                    refine ⟨382833204169410551408711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4083554177807045881692917 382833204169410551408711)
                    ·
                      rfl

theorem cell23_2236695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_2236695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236695 prefixEnd_2236695 := by exact prefixLift 2236695
  have htrace : WordTrace (prefixWord ++ tailWord_2236695) baseStart_2236695 baseEnd_2236695 := by
    simpa [prefixWord, tailWord_2236695, baseEnd_2236695] using wordTrace_append hprefix tailTrace_2236695
  have hstable : (prefixWord ++ tailWord_2236695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236695).length < 2 ^ (prefixWord ++ tailWord_2236695).sum := by decide
  have hdescent : baseEnd_2236695 < baseStart_2236695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236725 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2236725 : Nat := 118140960795 + 2236725 * 2 ^ 59
def prefixEnd_2236725 : Nat := 4983230072969 + 3 ^ 40 * 2236725 * 2
def baseEnd_2236725 : Nat := 382838338975955512283665

theorem tailTrace_2236725 : CollatzResearch.WordTrace tailWord_2236725 prefixEnd_2236725 382838338975955512283665 := by
  unfold tailWord_2236725
  simp only [CollatzResearch.WordTrace]
  refine ⟨81580062821734802062359629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54386708547823201374906419 81580062821734802062359629)
  ·
    refine ⟨30592523558150550773384861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81580062821734802062359629 30592523558150550773384861)
    ·
      refine ⟨11472196334306456540019323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30592523558150550773384861 11472196334306456540019323)
      ·
        refine ⟨17208294501459684810028985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11472196334306456540019323 17208294501459684810028985)
        ·
          refine ⟨12906220876094763607521739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17208294501459684810028985 12906220876094763607521739)
          ·
            refine ⟨19359331314142145411282609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12906220876094763607521739 19359331314142145411282609)
            ·
              refine ⟨14519498485606609058461957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19359331314142145411282609 14519498485606609058461957)
              ·
                refine ⟨2722405966051239198461617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14519498485606609058461957 2722405966051239198461617)
                ·
                  refine ⟨2041804474538429398846213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2722405966051239198461617 2041804474538429398846213)
                  ·
                    refine ⟨382838338975955512283665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2041804474538429398846213 382838338975955512283665)
                    ·
                      rfl

theorem cell23_2236725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2236725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236725 prefixEnd_2236725 := by exact prefixLift 2236725
  have htrace : WordTrace (prefixWord ++ tailWord_2236725) baseStart_2236725 baseEnd_2236725 := by
    simpa [prefixWord, tailWord_2236725, baseEnd_2236725] using wordTrace_append hprefix tailTrace_2236725
  have hstable : (prefixWord ++ tailWord_2236725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236725).length < 2 ^ (prefixWord ++ tailWord_2236725).sum := by decide
  have hdescent : baseEnd_2236725 < baseStart_2236725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236751 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 4, 7]
def baseStart_2236751 : Nat := 118140960795 + 2236751 * 2 ^ 59
def prefixEnd_2236751 : Nat := 4983230072969 + 3 ^ 40 * 2236751 * 2
def baseEnd_2236751 : Nat := 382842789141627811708625

theorem tailTrace_2236751 : CollatzResearch.WordTrace tailWord_2236751 prefixEnd_2236751 382842789141627811708625 := by
  unfold tailWord_2236751
  simp only [CollatzResearch.WordTrace]
  refine ⟨81581011119640608502806107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54387340746427072335204071 81581011119640608502806107)
  ·
    refine ⟨122371516679460912754209161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81581011119640608502806107 122371516679460912754209161)
    ·
      refine ⟨91778637509595684565656871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122371516679460912754209161 91778637509595684565656871)
      ·
        refine ⟨137667956264393526848485307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91778637509595684565656871 137667956264393526848485307)
        ·
          refine ⟨206501934396590290272727961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137667956264393526848485307 206501934396590290272727961)
          ·
            refine ⟨154876450797442717704545971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206501934396590290272727961 154876450797442717704545971)
            ·
              refine ⟨232314676196164076556818957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154876450797442717704545971 232314676196164076556818957)
              ·
                refine ⟨87118003573561528708807109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232314676196164076556818957 87118003573561528708807109)
                ·
                  refine ⟨16334625670042786632901333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87118003573561528708807109 16334625670042786632901333)
                  ·
                    refine ⟨382842789141627811708625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16334625670042786632901333 382842789141627811708625)
                    ·
                      rfl

theorem cell23_2236751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_2236751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236751 prefixEnd_2236751 := by exact prefixLift 2236751
  have htrace : WordTrace (prefixWord ++ tailWord_2236751) baseStart_2236751 baseEnd_2236751 := by
    simpa [prefixWord, tailWord_2236751, baseEnd_2236751] using wordTrace_append hprefix tailTrace_2236751
  have hstable : (prefixWord ++ tailWord_2236751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236751).length < 2 ^ (prefixWord ++ tailWord_2236751).sum := by decide
  have hdescent : baseEnd_2236751 < baseStart_2236751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236752 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3]
def baseStart_2236752 : Nat := 118140960795 + 2236752 * 2 ^ 59
def prefixEnd_2236752 : Nat := 4983230072969 + 3 ^ 40 * 2236752 * 2
def baseEnd_2236752 : Nat := 1148528880905537931213371

theorem tailTrace_2236752 : CollatzResearch.WordTrace tailWord_2236752 prefixEnd_2236752 1148528880905537931213371 := by
  unfold tailWord_2236752
  simp only [CollatzResearch.WordTrace]
  refine ⟨40790523796318492836796255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54387365061757990449061673 40790523796318492836796255)
  ·
    refine ⟨61185785694477739255194383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40790523796318492836796255 61185785694477739255194383)
    ·
      refine ⟨91778678541716608882791575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61185785694477739255194383 91778678541716608882791575)
      ·
        refine ⟨137668017812574913324187363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91778678541716608882791575 137668017812574913324187363)
        ·
          refine ⟨206502026718862369986281045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137668017812574913324187363 206502026718862369986281045)
          ·
            refine ⟨2419945625611668398276731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 206502026718862369986281045 2419945625611668398276731)
            ·
              refine ⟨3629918438417502597415097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419945625611668398276731 3629918438417502597415097)
              ·
                refine ⟨2722438828813126948061323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629918438417502597415097 2722438828813126948061323)
                ·
                  refine ⟨4083658243219690422091985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722438828813126948061323 4083658243219690422091985)
                  ·
                    refine ⟨3062743682414767816568989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4083658243219690422091985 3062743682414767816568989)
                    ·
                      refine ⟨1148528880905537931213371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062743682414767816568989 1148528880905537931213371)
                      ·
                        rfl

theorem cell23_2236752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_2236752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236752 prefixEnd_2236752 := by exact prefixLift 2236752
  have htrace : WordTrace (prefixWord ++ tailWord_2236752) baseStart_2236752 baseEnd_2236752 := by
    simpa [prefixWord, tailWord_2236752, baseEnd_2236752] using wordTrace_append hprefix tailTrace_2236752
  have hstable : (prefixWord ++ tailWord_2236752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236752).length < 2 ^ (prefixWord ++ tailWord_2236752).sum := by decide
  have hdescent : baseEnd_2236752 < baseStart_2236752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236826 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2]
def baseStart_2236826 : Nat := 118140960795 + 2236826 * 2 ^ 59
def prefixEnd_2236826 : Nat := 4983230072969 + 3 ^ 40 * 2236826 * 2
def baseEnd_2236826 : Nat := 1148566878473970641688031

theorem tailTrace_2236826 : CollatzResearch.WordTrace tailWord_2236826 prefixEnd_2236826 1148566878473970641688031 := by
  unfold tailWord_2236826
  simp only [CollatzResearch.WordTrace]
  refine ⟨20395936648592224077946583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54389164396245930874524221 20395936648592224077946583)
  ·
    refine ⟨30593904972888336116919875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20395936648592224077946583 30593904972888336116919875)
    ·
      refine ⟨45890857459332504175379813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30593904972888336116919875 45890857459332504175379813)
      ·
        refine ⟨8604535773624844532883715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45890857459332504175379813 8604535773624844532883715)
        ·
          refine ⟨12906803660437266799325573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604535773624844532883715 12906803660437266799325573)
          ·
            refine ⟨2420025686331987524873545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12906803660437266799325573 2420025686331987524873545)
            ·
              refine ⟨1815019264748990643655159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420025686331987524873545 1815019264748990643655159)
              ·
                refine ⟨2722528897123485965482739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815019264748990643655159 2722528897123485965482739)
                ·
                  refine ⟨4083793345685228948224109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722528897123485965482739 4083793345685228948224109)
                  ·
                    refine ⟨1531422504631960855584041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4083793345685228948224109 1531422504631960855584041)
                    ·
                      refine ⟨1148566878473970641688031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531422504631960855584041 1148566878473970641688031)
                      ·
                        rfl

theorem cell23_2236826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_2236826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236826 prefixEnd_2236826 := by exact prefixLift 2236826
  have htrace : WordTrace (prefixWord ++ tailWord_2236826) baseStart_2236826 baseEnd_2236826 := by
    simpa [prefixWord, tailWord_2236826, baseEnd_2236826] using wordTrace_append hprefix tailTrace_2236826
  have hstable : (prefixWord ++ tailWord_2236826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236826).length < 2 ^ (prefixWord ++ tailWord_2236826).sum := by decide
  have hdescent : baseEnd_2236826 < baseStart_2236826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236833 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2236833 : Nat := 118140960795 + 2236833 * 2 ^ 59
def prefixEnd_2236833 : Nat := 4983230072969 + 3 ^ 40 * 2236833 * 2
def baseEnd_2236833 : Nat := 1148570472838552114300499

theorem tailTrace_2236833 : CollatzResearch.WordTrace tailWord_2236833 prefixEnd_2236833 1148570472838552114300499 := by
  unfold tailWord_2236833
  simp only [CollatzResearch.WordTrace]
  refine ⟨81584001905343536507291153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54389334603562357671527435 81584001905343536507291153)
  ·
    refine ⟨61188001429007652380468365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81584001905343536507291153 61188001429007652380468365)
    ·
      refine ⟨22945500535877869642675637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61188001429007652380468365 22945500535877869642675637)
      ·
        refine ⟨2151140675238550279000841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22945500535877869642675637 2151140675238550279000841)
        ·
          refine ⟨1613355506428912709250631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151140675238550279000841 1613355506428912709250631)
          ·
            refine ⟨2420033259643369063875947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613355506428912709250631 2420033259643369063875947)
            ·
              refine ⟨3630049889465053595813921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420033259643369063875947 3630049889465053595813921)
              ·
                refine ⟨2722537417098790196860441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630049889465053595813921 2722537417098790196860441)
                ·
                  refine ⟨2041903062824092647645331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2722537417098790196860441 2041903062824092647645331)
                  ·
                    refine ⟨3062854594236138971467997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2041903062824092647645331 3062854594236138971467997)
                    ·
                      refine ⟨1148570472838552114300499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062854594236138971467997 1148570472838552114300499)
                      ·
                        rfl

theorem cell23_2236833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2236833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236833 prefixEnd_2236833 := by exact prefixLift 2236833
  have htrace : WordTrace (prefixWord ++ tailWord_2236833) baseStart_2236833 baseEnd_2236833 := by
    simpa [prefixWord, tailWord_2236833, baseEnd_2236833] using wordTrace_append hprefix tailTrace_2236833
  have hstable : (prefixWord ++ tailWord_2236833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236833).length < 2 ^ (prefixWord ++ tailWord_2236833).sum := by decide
  have hdescent : baseEnd_2236833 < baseStart_2236833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236839 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_2236839 : Nat := 118140960795 + 2236839 * 2 ^ 59
def prefixEnd_2236839 : Nat := 4983230072969 + 3 ^ 40 * 2236839 * 2
def baseEnd_2236839 : Nat := 1148573553722479090825471

theorem tailTrace_2236839 : CollatzResearch.WordTrace tailWord_2236839 prefixEnd_2236839 1148573553722479090825471 := by
  unfold tailWord_2236839
  simp only [CollatzResearch.WordTrace]
  refine ⟨81584220743321799532009571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54389480495547866354673047 81584220743321799532009571)
  ·
    refine ⟨122376331114982699298014357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81584220743321799532009571 122376331114982699298014357)
    ·
      refine ⟨5736390521014814029594423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122376331114982699298014357 5736390521014814029594423)
      ·
        refine ⟨8604585781522221044391635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736390521014814029594423 8604585781522221044391635)
        ·
          refine ⟨12906878672283331566587453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604585781522221044391635 12906878672283331566587453)
          ·
            refine ⟨4840079502106249337470295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12906878672283331566587453 4840079502106249337470295)
            ·
              refine ⟨7260119253159374006205443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840079502106249337470295 7260119253159374006205443)
              ·
                refine ⟨10890178879739061009308165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7260119253159374006205443 10890178879739061009308165)
                ·
                  refine ⟨2041908539951073939245281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10890178879739061009308165 2041908539951073939245281)
                  ·
                    refine ⟨1531431404963305454433961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2041908539951073939245281 1531431404963305454433961)
                    ·
                      refine ⟨1148573553722479090825471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531431404963305454433961 1148573553722479090825471)
                      ·
                        rfl

theorem cell23_2236839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_2236839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236839 prefixEnd_2236839 := by exact prefixLift 2236839
  have htrace : WordTrace (prefixWord ++ tailWord_2236839) baseStart_2236839 baseEnd_2236839 := by
    simpa [prefixWord, tailWord_2236839, baseEnd_2236839] using wordTrace_append hprefix tailTrace_2236839
  have hstable : (prefixWord ++ tailWord_2236839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236839).length < 2 ^ (prefixWord ++ tailWord_2236839).sum := by decide
  have hdescent : baseEnd_2236839 < baseStart_2236839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236855 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_2236855 : Nat := 118140960795 + 2236855 * 2 ^ 59
def prefixEnd_2236855 : Nat := 4983230072969 + 3 ^ 40 * 2236855 * 2
def baseEnd_2236855 : Nat := 1148581769412951028225397

theorem tailTrace_2236855 : CollatzResearch.WordTrace tailWord_2236855 prefixEnd_2236855 1148581769412951028225397 := by
  unfold tailWord_2236855
  simp only [CollatzResearch.WordTrace]
  refine ⟨81584804311263834264592019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54389869540842556176394679 81584804311263834264592019)
  ·
    refine ⟨122377206466895751396888029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81584804311263834264592019 122377206466895751396888029)
    ·
      refine ⟨45891452425085906773833011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122377206466895751396888029 45891452425085906773833011)
      ·
        refine ⟨68837178637628860160749517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45891452425085906773833011 68837178637628860160749517)
        ·
          refine ⟨25813941989110822560281069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68837178637628860160749517 25813941989110822560281069)
          ·
            refine ⟨9680228245916558460105401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25813941989110822560281069 9680228245916558460105401)
            ·
              refine ⟨7260171184437418845079051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9680228245916558460105401 7260171184437418845079051)
              ·
                refine ⟨10890256776656128267618577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7260171184437418845079051 10890256776656128267618577)
                ·
                  refine ⟨8167692582492096200713933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10890256776656128267618577 8167692582492096200713933)
                  ·
                    refine ⟨3062884718434536075267725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8167692582492096200713933 3062884718434536075267725)
                    ·
                      refine ⟨1148581769412951028225397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062884718434536075267725 1148581769412951028225397)
                      ·
                        rfl

theorem cell23_2236855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_2236855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236855 prefixEnd_2236855 := by exact prefixLift 2236855
  have htrace : WordTrace (prefixWord ++ tailWord_2236855) baseStart_2236855 baseEnd_2236855 := by
    simpa [prefixWord, tailWord_2236855, baseEnd_2236855] using wordTrace_append hprefix tailTrace_2236855
  have hstable : (prefixWord ++ tailWord_2236855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236855).length < 2 ^ (prefixWord ++ tailWord_2236855).sum := by decide
  have hdescent : baseEnd_2236855 < baseStart_2236855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236895 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_2236895 : Nat := 118140960795 + 2236895 * 2 ^ 59
def prefixEnd_2236895 : Nat := 4983230072969 + 3 ^ 40 * 2236895 * 2
def baseEnd_2236895 : Nat := 1148602308639130871725213

theorem tailTrace_2236895 : CollatzResearch.WordTrace tailWord_2236895 prefixEnd_2236895 1148602308639130871725213 := by
  unfold tailWord_2236895
  simp only [CollatzResearch.WordTrace]
  refine ⟨81586263231118921096048139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54390842154079280730698759 81586263231118921096048139)
  ·
    refine ⟨122379394846678381644072209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81586263231118921096048139 122379394846678381644072209)
    ·
      refine ⟨91784546135008786233054157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122379394846678381644072209 91784546135008786233054157)
      ·
        refine ⟨34419204800628294837395309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91784546135008786233054157 34419204800628294837395309)
        ·
          refine ⟨12907201800235610564023241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34419204800628294837395309 12907201800235610564023241)
          ·
            refine ⟨9680401350176707923017431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12907201800235610564023241 9680401350176707923017431)
            ·
              refine ⟨14520602025265061884526147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9680401350176707923017431 14520602025265061884526147)
              ·
                refine ⟨21780903037897592826789221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14520602025265061884526147 21780903037897592826789221)
                ·
                  refine ⟨4083919319605798655022979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21780903037897592826789221 4083919319605798655022979)
                  ·
                    refine ⟨6125878979408697982534469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083919319605798655022979 6125878979408697982534469)
                    ·
                      refine ⟨1148602308639130871725213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6125878979408697982534469 1148602308639130871725213)
                      ·
                        rfl

theorem cell23_2236895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_2236895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236895 prefixEnd_2236895 := by exact prefixLift 2236895
  have htrace : WordTrace (prefixWord ++ tailWord_2236895) baseStart_2236895 baseEnd_2236895 := by
    simpa [prefixWord, tailWord_2236895, baseEnd_2236895] using wordTrace_append hprefix tailTrace_2236895
  have hstable : (prefixWord ++ tailWord_2236895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236895).length < 2 ^ (prefixWord ++ tailWord_2236895).sum := by decide
  have hdescent : baseEnd_2236895 < baseStart_2236895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236905 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 3, 4]
def baseStart_2236905 : Nat := 118140960795 + 2236905 * 2 ^ 59
def prefixEnd_2236905 : Nat := 4983230072969 + 3 ^ 40 * 2236905 * 2
def baseEnd_2236905 : Nat := 382869147815225277533389

theorem tailTrace_2236905 : CollatzResearch.WordTrace tailWord_2236905 prefixEnd_2236905 382869147815225277533389 := by
  unfold tailWord_2236905
  simp only [CollatzResearch.WordTrace]
  refine ⟨81586627961082692803912169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54391085307388461869274779 81586627961082692803912169)
  ·
    refine ⟨61189970970812019602934127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81586627961082692803912169 61189970970812019602934127)
    ·
      refine ⟨91784956456218029404401191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61189970970812019602934127 91784956456218029404401191)
      ·
        refine ⟨137677434684327044106601787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91784956456218029404401191 137677434684327044106601787)
        ·
          refine ⟨206516152026490566159902681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137677434684327044106601787 206516152026490566159902681)
          ·
            refine ⟨154887114019867924619927011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206516152026490566159902681 154887114019867924619927011)
            ·
              refine ⟨232330671029801886929890517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154887114019867924619927011 232330671029801886929890517)
              ·
                refine ⟨5445250102260981724919309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232330671029801886929890517 5445250102260981724919309)
                ·
                  refine ⟨2041968788347868146844741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5445250102260981724919309 2041968788347868146844741)
                  ·
                    refine ⟨382869147815225277533389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2041968788347868146844741 382869147815225277533389)
                    ·
                      rfl

theorem cell23_2236905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_2236905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236905 prefixEnd_2236905 := by exact prefixLift 2236905
  have htrace : WordTrace (prefixWord ++ tailWord_2236905) baseStart_2236905 baseEnd_2236905 := by
    simpa [prefixWord, tailWord_2236905, baseEnd_2236905] using wordTrace_append hprefix tailTrace_2236905
  have hstable : (prefixWord ++ tailWord_2236905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236905).length < 2 ^ (prefixWord ++ tailWord_2236905).sum := by decide
  have hdescent : baseEnd_2236905 < baseStart_2236905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236915 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 3]
def baseStart_2236915 : Nat := 118140960795 + 2236915 * 2 ^ 59
def prefixEnd_2236915 : Nat := 4983230072969 + 3 ^ 40 * 2236915 * 2
def baseEnd_2236915 : Nat := 1148612578252220793475121

theorem tailTrace_2236915 : CollatzResearch.WordTrace tailWord_2236915 prefixEnd_2236915 1148612578252220793475121 := by
  unfold tailWord_2236915
  simp only [CollatzResearch.WordTrace]
  refine ⟨81586992691046464511776199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54391328460697643007850799 81586992691046464511776199)
  ·
    refine ⟨122380489036569696767664299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81586992691046464511776199 122380489036569696767664299)
    ·
      refine ⟨183570733554854545151496449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122380489036569696767664299 183570733554854545151496449)
      ·
        refine ⟨137678050166140908863622337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183570733554854545151496449 137678050166140908863622337)
        ·
          refine ⟨103258537624605681647716753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137678050166140908863622337 103258537624605681647716753)
          ·
            refine ⟨77443903218454261235787565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103258537624605681647716753 77443903218454261235787565)
            ·
              refine ⟨29041463706920347963420337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77443903218454261235787565 29041463706920347963420337)
              ·
                refine ⟨21781097780190260972565253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29041463706920347963420337 21781097780190260972565253)
                ·
                  refine ⟨4083955833785673932355985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21781097780190260972565253 4083955833785673932355985)
                  ·
                    refine ⟨3062966875339255449266989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4083955833785673932355985 3062966875339255449266989)
                    ·
                      refine ⟨1148612578252220793475121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3062966875339255449266989 1148612578252220793475121)
                      ·
                        rfl

theorem cell23_2236915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_2236915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236915 prefixEnd_2236915 := by exact prefixLift 2236915
  have htrace : WordTrace (prefixWord ++ tailWord_2236915) baseStart_2236915 baseEnd_2236915 := by
    simpa [prefixWord, tailWord_2236915, baseEnd_2236915] using wordTrace_append hprefix tailTrace_2236915
  have hstable : (prefixWord ++ tailWord_2236915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236915).length < 2 ^ (prefixWord ++ tailWord_2236915).sum := by decide
  have hdescent : baseEnd_2236915 < baseStart_2236915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236952 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 6]
def baseStart_2236952 : Nat := 118140960795 + 2236952 * 2 ^ 59
def prefixEnd_2236952 : Nat := 4983230072969 + 3 ^ 40 * 2236952 * 2
def baseEnd_2236952 : Nat := 127625730781826349856939

theorem tailTrace_2236952 : CollatzResearch.WordTrace tailWord_2236952 prefixEnd_2236952 127625730781826349856939 := by
  unfold tailWord_2236952
  simp only [CollatzResearch.WordTrace]
  refine ⟨40794171095956209915436555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54392228127941613220582073 40794171095956209915436555)
  ·
    refine ⟨61191256643934314873154833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40794171095956209915436555 61191256643934314873154833)
    ·
      refine ⟨45893442482950736154866125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61191256643934314873154833 45893442482950736154866125)
      ·
        refine ⟨17210040931106526058074797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45893442482950736154866125 17210040931106526058074797)
        ·
          refine ⟨6453765349164947271778049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17210040931106526058074797 6453765349164947271778049)
          ·
            refine ⟨4840324011873710453833537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6453765349164947271778049 4840324011873710453833537)
            ·
              refine ⟨3630243008905282840375153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4840324011873710453833537 3630243008905282840375153)
              ·
                refine ⟨2722682256678962130281365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630243008905282840375153 2722682256678962130281365)
                ·
                  refine ⟨127625730781826349856939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2722682256678962130281365 127625730781826349856939)
                  ·
                    rfl

theorem cell23_2236952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 6].length) (baseStart_2236952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236952 prefixEnd_2236952 := by exact prefixLift 2236952
  have htrace : WordTrace (prefixWord ++ tailWord_2236952) baseStart_2236952 baseEnd_2236952 := by
    simpa [prefixWord, tailWord_2236952, baseEnd_2236952] using wordTrace_append hprefix tailTrace_2236952
  have hstable : (prefixWord ++ tailWord_2236952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236952).length < 2 ^ (prefixWord ++ tailWord_2236952).sum := by decide
  have hdescent : baseEnd_2236952 < baseStart_2236952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236956 : List Nat := [2, 2, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_2236956 : Nat := 118140960795 + 2236956 * 2 ^ 59
def prefixEnd_2236956 : Nat := 4983230072969 + 3 ^ 40 * 2236956 * 2
def baseEnd_2236956 : Nat := 382877876986351711020811

theorem tailTrace_2236956 : CollatzResearch.WordTrace tailWord_2236956 prefixEnd_2236956 382877876986351711020811 := by
  unfold tailWord_2236956
  simp only [CollatzResearch.WordTrace]
  refine ⟨40794244041948964257009361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54392325389265285676012481 40794244041948964257009361)
  ·
    refine ⟨30595683031461723192757021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40794244041948964257009361 30595683031461723192757021)
    ·
      refine ⟨11473381136798146197283883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30595683031461723192757021 11473381136798146197283883)
      ·
        refine ⟨17210071705197219295925825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11473381136798146197283883 17210071705197219295925825)
        ·
          refine ⟨12907553778897914471944369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17210071705197219295925825 12907553778897914471944369)
          ·
            refine ⟨9680665334173435853958277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12907553778897914471944369 9680665334173435853958277)
            ·
              refine ⟨1815124750157519222617177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9680665334173435853958277 1815124750157519222617177)
              ·
                refine ⟨1361343562618139416962883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815124750157519222617177 1361343562618139416962883)
                ·
                  refine ⟨2042015343927209125444325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361343562618139416962883 2042015343927209125444325)
                  ·
                    refine ⟨382877876986351711020811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042015343927209125444325 382877876986351711020811)
                    ·
                      rfl

theorem cell23_2236956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_2236956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236956 prefixEnd_2236956 := by exact prefixLift 2236956
  have htrace : WordTrace (prefixWord ++ tailWord_2236956) baseStart_2236956 baseEnd_2236956 := by
    simpa [prefixWord, tailWord_2236956, baseEnd_2236956] using wordTrace_append hprefix tailTrace_2236956
  have hstable : (prefixWord ++ tailWord_2236956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236956).length < 2 ^ (prefixWord ++ tailWord_2236956).sum := by decide
  have hdescent : baseEnd_2236956 < baseStart_2236956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236965 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_2236965 : Nat := 118140960795 + 2236965 * 2 ^ 59
def prefixEnd_2236965 : Nat := 4983230072969 + 3 ^ 40 * 2236965 * 2
def baseEnd_2236965 : Nat := 382879417428315199283297

theorem tailTrace_2236965 : CollatzResearch.WordTrace tailWord_2236965 prefixEnd_2236965 382879417428315199283297 := by
  unfold tailWord_2236965
  simp only [CollatzResearch.WordTrace]
  refine ⟨81588816340865323051096349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54392544227243548700730899 81588816340865323051096349)
  ·
    refine ⟨30595806127824496144161131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81588816340865323051096349 30595806127824496144161131)
    ·
      refine ⟨45893709191736744216241697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30595806127824496144161131 45893709191736744216241697)
      ·
        refine ⟨34420281893802558162181273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45893709191736744216241697 34420281893802558162181273)
        ·
          refine ⟨25815211420351918621635955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34420281893802558162181273 25815211420351918621635955)
          ·
            refine ⟨38722817130527877932453933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25815211420351918621635955 38722817130527877932453933)
            ·
              refine ⟨14521056423947954224670225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38722817130527877932453933 14521056423947954224670225)
              ·
                refine ⟨10890792317960965668502669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14521056423947954224670225 10890792317960965668502669)
                ·
                  refine ⟨4084047119235362125688501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10890792317960965668502669 4084047119235362125688501)
                  ·
                    refine ⟨382879417428315199283297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4084047119235362125688501 382879417428315199283297)
                    ·
                      rfl

theorem cell23_2236965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_2236965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236965 prefixEnd_2236965 := by exact prefixLift 2236965
  have htrace : WordTrace (prefixWord ++ tailWord_2236965) baseStart_2236965 baseEnd_2236965 := by
    simpa [prefixWord, tailWord_2236965, baseEnd_2236965] using wordTrace_append hprefix tailTrace_2236965
  have hstable : (prefixWord ++ tailWord_2236965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236965).length < 2 ^ (prefixWord ++ tailWord_2236965).sum := by decide
  have hdescent : baseEnd_2236965 < baseStart_2236965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236972 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 4, 3, 2]
def baseStart_2236972 : Nat := 118140960795 + 2236972 * 2 ^ 59
def prefixEnd_2236972 : Nat := 4983230072969 + 3 ^ 40 * 2236972 * 2
def baseEnd_2236972 : Nat := 1148641846649527070462359

theorem tailTrace_2236972 : CollatzResearch.WordTrace tailWord_2236972 prefixEnd_2236972 1148641846649527070462359 := by
  unfold tailWord_2236972
  simp only [CollatzResearch.WordTrace]
  refine ⟨40794535825919981623300585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54392714434559975497734113 40794535825919981623300585)
  ·
    refine ⟨30595901869439986217475439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40794535825919981623300585 30595901869439986217475439)
    ·
      refine ⟨45893852804159979326213159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30595901869439986217475439 45893852804159979326213159)
      ·
        refine ⟨68840779206239968989319739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45893852804159979326213159 68840779206239968989319739)
        ·
          refine ⟨103261168809359953483979609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68840779206239968989319739 103261168809359953483979609)
          ·
            refine ⟨77445876607019965112984707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103261168809359953483979609 77445876607019965112984707)
            ·
              refine ⟨116168814910529947669477061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77445876607019965112984707 116168814910529947669477061)
              ·
                refine ⟨21781652795724365188026949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116168814910529947669477061 21781652795724365188026949)
                ·
                  refine ⟨4084059899198318472755053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21781652795724365188026949 4084059899198318472755053)
                  ·
                    refine ⟨1531522462199369427283145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4084059899198318472755053 1531522462199369427283145)
                    ·
                      refine ⟨1148641846649527070462359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531522462199369427283145 1148641846649527070462359)
                      ·
                        rfl

theorem cell23_2236972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_2236972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236972 prefixEnd_2236972 := by exact prefixLift 2236972
  have htrace : WordTrace (prefixWord ++ tailWord_2236972) baseStart_2236972 baseEnd_2236972 := by
    simpa [prefixWord, tailWord_2236972, baseEnd_2236972] using wordTrace_append hprefix tailTrace_2236972
  have hstable : (prefixWord ++ tailWord_2236972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236972).length < 2 ^ (prefixWord ++ tailWord_2236972).sum := by decide
  have hdescent : baseEnd_2236972 < baseStart_2236972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236973 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2236973 : Nat := 118140960795 + 2236973 * 2 ^ 59
def prefixEnd_2236973 : Nat := 4983230072969 + 3 ^ 40 * 2236973 * 2
def baseEnd_2236973 : Nat := 382880786710060522183285

theorem tailTrace_2236973 : CollatzResearch.WordTrace tailWord_2236973 prefixEnd_2236973 382880786710060522183285 := by
  unfold tailWord_2236973
  simp only [CollatzResearch.WordTrace]
  refine ⟨81589108124836340417387573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54392738749890893611591715 81589108124836340417387573)
  ·
    refine ⟨7648978886703406914130085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81589108124836340417387573 7648978886703406914130085)
    ·
      refine ⟨1434183541256888796399391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7648978886703406914130085 1434183541256888796399391)
      ·
        refine ⟨2151275311885333194599087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434183541256888796399391 2151275311885333194599087)
        ·
          refine ⟨3226912967827999791898631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151275311885333194599087 3226912967827999791898631)
          ·
            refine ⟨4840369451741999687847947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226912967827999791898631 4840369451741999687847947)
            ·
              refine ⟨7260554177612999531771921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840369451741999687847947 7260554177612999531771921)
              ·
                refine ⟨5445415633209749648828941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7260554177612999531771921 5445415633209749648828941)
                ·
                  refine ⟨2042030862453656118310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5445415633209749648828941 2042030862453656118310853)
                  ·
                    refine ⟨382880786710060522183285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042030862453656118310853 382880786710060522183285)
                    ·
                      rfl

theorem cell23_2236973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2236973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236973 prefixEnd_2236973 := by exact prefixLift 2236973
  have htrace : WordTrace (prefixWord ++ tailWord_2236973) baseStart_2236973 baseEnd_2236973 := by
    simpa [prefixWord, tailWord_2236973, baseEnd_2236973] using wordTrace_append hprefix tailTrace_2236973
  have hstable : (prefixWord ++ tailWord_2236973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236973).length < 2 ^ (prefixWord ++ tailWord_2236973).sum := by decide
  have hdescent : baseEnd_2236973 < baseStart_2236973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236989 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_2236989 : Nat := 118140960795 + 2236989 * 2 ^ 59
def prefixEnd_2236989 : Nat := 4983230072969 + 3 ^ 40 * 2236989 * 2
def baseEnd_2236989 : Nat := 1148650575820653503949781

theorem tailTrace_2236989 : CollatzResearch.WordTrace tailWord_2236989 prefixEnd_2236989 1148650575820653503949781 := by
  unfold tailWord_2236989
  simp only [CollatzResearch.WordTrace]
  refine ⟨81589691692778375149970021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54393127795185583433313347 81589691692778375149970021)
  ·
    refine ⟨15298067192395945340619379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81589691692778375149970021 15298067192395945340619379)
    ·
      refine ⟨22947100788593918010929069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15298067192395945340619379 22947100788593918010929069)
      ·
        refine ⟨8605162795722719254098401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22947100788593918010929069 8605162795722719254098401)
        ·
          refine ⟨6453872096792039440573801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8605162795722719254098401 6453872096792039440573801)
          ·
            refine ⟨4840404072594029580430351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6453872096792039440573801 4840404072594029580430351)
            ·
              refine ⟨7260606108891044370645527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840404072594029580430351 7260606108891044370645527)
              ·
                refine ⟨10890909163336566555968291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7260606108891044370645527 10890909163336566555968291)
                ·
                  refine ⟨16336363745004849833952437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10890909163336566555968291 16336363745004849833952437)
                  ·
                    refine ⟨1531534101094204671933041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16336363745004849833952437 1531534101094204671933041)
                    ·
                      refine ⟨1148650575820653503949781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531534101094204671933041 1148650575820653503949781)
                      ·
                        rfl

theorem cell23_2236989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_2236989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236989 prefixEnd_2236989 := by exact prefixLift 2236989
  have htrace : WordTrace (prefixWord ++ tailWord_2236989) baseStart_2236989 baseEnd_2236989 := by
    simpa [prefixWord, tailWord_2236989, baseEnd_2236989] using wordTrace_append hprefix tailTrace_2236989
  have hstable : (prefixWord ++ tailWord_2236989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236989).length < 2 ^ (prefixWord ++ tailWord_2236989).sum := by decide
  have hdescent : baseEnd_2236989 < baseStart_2236989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236999 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 1, 5]
def baseStart_2236999 : Nat := 118140960795 + 2236999 * 2 ^ 59
def prefixEnd_2236999 : Nat := 4983230072969 + 3 ^ 40 * 2236999 * 2
def baseEnd_2236999 : Nat := 382885236875732821608245

theorem tailTrace_2236999 : CollatzResearch.WordTrace tailWord_2236999 prefixEnd_2236999 382885236875732821608245 := by
  unfold tailWord_2236999
  simp only [CollatzResearch.WordTrace]
  refine ⟨81590056422742146857834051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54393370948494764571889367 81590056422742146857834051)
  ·
    refine ⟨122385084634113220286751077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81590056422742146857834051 122385084634113220286751077)
    ·
      refine ⟨22947203368896228803765827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122385084634113220286751077 22947203368896228803765827)
      ·
        refine ⟨34420805053344343205648741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22947203368896228803765827 34420805053344343205648741)
        ·
          refine ⟨6453900947502064351059139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34420805053344343205648741 6453900947502064351059139)
          ·
            refine ⟨9680851421253096526588709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6453900947502064351059139 9680851421253096526588709)
            ·
              refine ⟨1815159641484955598735383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9680851421253096526588709 1815159641484955598735383)
              ·
                refine ⟨2722739462227433398103075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815159641484955598735383 2722739462227433398103075)
                ·
                  refine ⟨4084109193341150097154613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722739462227433398103075 4084109193341150097154613)
                  ·
                    refine ⟨382885236875732821608245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4084109193341150097154613 382885236875732821608245)
                    ·
                      rfl

theorem cell23_2236999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_2236999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2236999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2236999 prefixEnd_2236999 := by exact prefixLift 2236999
  have htrace : WordTrace (prefixWord ++ tailWord_2236999) baseStart_2236999 baseEnd_2236999 := by
    simpa [prefixWord, tailWord_2236999, baseEnd_2236999] using wordTrace_append hprefix tailTrace_2236999
  have hstable : (prefixWord ++ tailWord_2236999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236999).length < 2 ^ (prefixWord ++ tailWord_2236999).sum := by decide
  have hdescent : baseEnd_2236999 < baseStart_2236999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237015 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_2237015 : Nat := 118140960795 + 2237015 * 2 ^ 59
def prefixEnd_2237015 : Nat := 4983230072969 + 3 ^ 40 * 2237015 * 2
def baseEnd_2237015 : Nat := 1148663926317670402224661

theorem tailTrace_2237015 : CollatzResearch.WordTrace tailWord_2237015 prefixEnd_2237015 1148663926317670402224661 := by
  unfold tailWord_2237015
  simp only [CollatzResearch.WordTrace]
  refine ⟨81590639990684181590416499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54393759993789454393610999 81590639990684181590416499)
  ·
    refine ⟨122385959986026272385624749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81590639990684181590416499 122385959986026272385624749)
    ·
      refine ⟨45894734994759852144609281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122385959986026272385624749 45894734994759852144609281)
      ·
        refine ⟨34421051246069889108456961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45894734994759852144609281 34421051246069889108456961)
        ·
          refine ⟨25815788434552416831342721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34421051246069889108456961 25815788434552416831342721)
          ·
            refine ⟨19361841325914312623507041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25815788434552416831342721 19361841325914312623507041)
            ·
              refine ⟨14521380994435734467630281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19361841325914312623507041 14521380994435734467630281)
              ·
                refine ⟨10891035745826800850722711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14521380994435734467630281 10891035745826800850722711)
                ·
                  refine ⟨16336553618740201276084067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10891035745826800850722711 16336553618740201276084067)
                  ·
                    refine ⟨24504830428110301914126101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16336553618740201276084067 24504830428110301914126101)
                    ·
                      refine ⟨1148663926317670402224661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24504830428110301914126101 1148663926317670402224661)
                      ·
                        rfl

theorem cell23_2237015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_2237015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237015 prefixEnd_2237015 := by exact prefixLift 2237015
  have htrace : WordTrace (prefixWord ++ tailWord_2237015) baseStart_2237015 baseEnd_2237015 := by
    simpa [prefixWord, tailWord_2237015, baseEnd_2237015] using wordTrace_append hprefix tailTrace_2237015
  have hstable : (prefixWord ++ tailWord_2237015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237015).length < 2 ^ (prefixWord ++ tailWord_2237015).sum := by decide
  have hdescent : baseEnd_2237015 < baseStart_2237015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237029 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_2237029 : Nat := 118140960795 + 2237029 * 2 ^ 59
def prefixEnd_2237029 : Nat := 4983230072969 + 3 ^ 40 * 2237029 * 2
def baseEnd_2237029 : Nat := 382890371682277782483199

theorem tailTrace_2237029 : CollatzResearch.WordTrace tailWord_2237029 prefixEnd_2237029 382890371682277782483199 := by
  unfold tailWord_2237029
  simp only [CollatzResearch.WordTrace]
  refine ⟨81591150612633461981426141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54394100408422307987617427 81591150612633461981426141)
  ·
    refine ⟨30596681479737548243034803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81591150612633461981426141 30596681479737548243034803)
    ·
      refine ⟨45895022219606322364552205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30596681479737548243034803 45895022219606322364552205)
      ·
        refine ⟨17210633332352370886707077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45895022219606322364552205 17210633332352370886707077)
        ·
          refine ⟨3226993749816069541257577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17210633332352370886707077 3226993749816069541257577)
          ·
            refine ⟨2420245312362052155943183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3226993749816069541257577 2420245312362052155943183)
            ·
              refine ⟨3630367968543078233914775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420245312362052155943183 3630367968543078233914775)
              ·
                refine ⟨5445551952814617350872163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630367968543078233914775 5445551952814617350872163)
                ·
                  refine ⟨8168327929221926026308245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445551952814617350872163 8168327929221926026308245)
                  ·
                    refine ⟨382890371682277782483199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8168327929221926026308245 382890371682277782483199)
                    ·
                      rfl

theorem cell23_2237029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_2237029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237029 prefixEnd_2237029 := by exact prefixLift 2237029
  have htrace : WordTrace (prefixWord ++ tailWord_2237029) baseStart_2237029 baseEnd_2237029 := by
    simpa [prefixWord, tailWord_2237029, baseEnd_2237029] using wordTrace_append hprefix tailTrace_2237029
  have hstable : (prefixWord ++ tailWord_2237029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237029).length < 2 ^ (prefixWord ++ tailWord_2237029).sum := by decide
  have hdescent : baseEnd_2237029 < baseStart_2237029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237042 : List Nat := [3, 2, 1, 2, 4, 1, 1, 9]
def baseStart_2237042 : Nat := 118140960795 + 2237042 * 2 ^ 59
def prefixEnd_2237042 : Nat := 4983230072969 + 3 ^ 40 * 2237042 * 2
def baseEnd_2237042 : Nat := 42543621862790436910631

theorem tailTrace_2237042 : CollatzResearch.WordTrace tailWord_2237042 prefixEnd_2237042 42543621862790436910631 := by
  unfold tailWord_2237042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20397906190396591300412345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54394416507724243467766253 20397906190396591300412345)
  ·
    refine ⟨15298429642797443475309259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20397906190396591300412345 15298429642797443475309259)
    ·
      refine ⟨22947644464196165212963889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15298429642797443475309259 22947644464196165212963889)
      ·
        refine ⟨17210733348147123909722917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22947644464196165212963889 17210733348147123909722917)
        ·
          refine ⟨3227012502777585733073047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17210733348147123909722917 3227012502777585733073047)
          ·
            refine ⟨4840518754166378599609571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3227012502777585733073047 4840518754166378599609571)
            ·
              refine ⟨7260778131249567899414357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840518754166378599609571 7260778131249567899414357)
              ·
                refine ⟨42543621862790436910631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7260778131249567899414357 42543621862790436910631)
                ·
                  rfl

theorem cell23_2237042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 9].length) (baseStart_2237042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237042 prefixEnd_2237042 := by exact prefixLift 2237042
  have htrace : WordTrace (prefixWord ++ tailWord_2237042) baseStart_2237042 baseEnd_2237042 := by
    simpa [prefixWord, tailWord_2237042, baseEnd_2237042] using wordTrace_append hprefix tailTrace_2237042
  have hstable : (prefixWord ++ tailWord_2237042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237042).length < 2 ^ (prefixWord ++ tailWord_2237042).sum := by decide
  have hdescent : baseEnd_2237042 < baseStart_2237042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237052 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_2237052 : Nat := 118140960795 + 2237052 * 2 ^ 59
def prefixEnd_2237052 : Nat := 4983230072969 + 3 ^ 40 * 2237052 * 2
def baseEnd_2237052 : Nat := 1148682925101886757461991

theorem tailTrace_2237052 : CollatzResearch.WordTrace tailWord_2237052 prefixEnd_2237052 1148682925101886757461991 := by
  unfold tailWord_2237052
  simp only [CollatzResearch.WordTrace]
  refine ⟨40795994745775068454756705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54394659661033424606342273 40795994745775068454756705)
  ·
    refine ⟨30596996059331301341067529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40795994745775068454756705 30596996059331301341067529)
    ·
      refine ⟨22947747044498476005800647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30596996059331301341067529 22947747044498476005800647)
      ·
        refine ⟨34421620566747714008700971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22947747044498476005800647 34421620566747714008700971)
        ·
          refine ⟨51632430850121571013051457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34421620566747714008700971 51632430850121571013051457)
          ·
            refine ⟨38724323137591178259788593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51632430850121571013051457 38724323137591178259788593)
            ·
              refine ⟨29043242353193383694841445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38724323137591178259788593 29043242353193383694841445)
              ·
                refine ⟨5445607941223759442782771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29043242353193383694841445 5445607941223759442782771)
                ·
                  refine ⟨8168411911835639164174157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445607941223759442782771 8168411911835639164174157)
                  ·
                    refine ⟨3063154466938364686565309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8168411911835639164174157 3063154466938364686565309)
                    ·
                      refine ⟨1148682925101886757461991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3063154466938364686565309 1148682925101886757461991)
                      ·
                        rfl

theorem cell23_2237052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_2237052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237052 prefixEnd_2237052 := by exact prefixLift 2237052
  have htrace : WordTrace (prefixWord ++ tailWord_2237052) baseStart_2237052 baseEnd_2237052 := by
    simpa [prefixWord, tailWord_2237052, baseEnd_2237052] using wordTrace_append hprefix tailTrace_2237052
  have hstable : (prefixWord ++ tailWord_2237052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237052).length < 2 ^ (prefixWord ++ tailWord_2237052).sum := by decide
  have hdescent : baseEnd_2237052 < baseStart_2237052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237065 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_2237065 : Nat := 118140960795 + 2237065 * 2 ^ 59
def prefixEnd_2237065 : Nat := 4983230072969 + 3 ^ 40 * 2237065 * 2
def baseEnd_2237065 : Nat := 1148689600350395206599431

theorem tailTrace_2237065 : CollatzResearch.WordTrace tailWord_2237065 prefixEnd_2237065 1148689600350395206599431 := by
  unfold tailWord_2237065
  simp only [CollatzResearch.WordTrace]
  refine ⟨81592463640503040129736649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54394975760335360086491099 81592463640503040129736649)
  ·
    refine ⟨61194347730377280097302487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81592463640503040129736649 61194347730377280097302487)
    ·
      refine ⟨91791521595565920145953731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61194347730377280097302487 91791521595565920145953731)
      ·
        refine ⟨137687282393348880218930597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91791521595565920145953731 137687282393348880218930597)
        ·
          refine ⟨25816365448752915041049487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137687282393348880218930597 25816365448752915041049487)
          ·
            refine ⟨38724548173129372561574231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25816365448752915041049487 38724548173129372561574231)
            ·
              refine ⟨58086822259694058842361347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38724548173129372561574231 58086822259694058842361347)
              ·
                refine ⟨87130233389541088263542021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58086822259694058842361347 87130233389541088263542021)
                ·
                  refine ⟨16336918760538954049414129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87130233389541088263542021 16336918760538954049414129)
                  ·
                    refine ⟨12252689070404215537060597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16336918760538954049414129 12252689070404215537060597)
                    ·
                      refine ⟨1148689600350395206599431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12252689070404215537060597 1148689600350395206599431)
                      ·
                        rfl

theorem cell23_2237065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_2237065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237065 prefixEnd_2237065 := by exact prefixLift 2237065
  have htrace : WordTrace (prefixWord ++ tailWord_2237065) baseStart_2237065 baseEnd_2237065 := by
    simpa [prefixWord, tailWord_2237065, baseEnd_2237065] using wordTrace_append hprefix tailTrace_2237065
  have hstable : (prefixWord ++ tailWord_2237065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237065).length < 2 ^ (prefixWord ++ tailWord_2237065).sum := by decide
  have hdescent : baseEnd_2237065 < baseStart_2237065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237070 : List Nat := [4, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2237070 : Nat := 118140960795 + 2237070 * 2 ^ 59
def prefixEnd_2237070 : Nat := 4983230072969 + 3 ^ 40 * 2237070 * 2
def baseEnd_2237070 : Nat := 1148692167753667687036909

theorem tailTrace_2237070 : CollatzResearch.WordTrace tailWord_2237070 prefixEnd_2237070 1148692167753667687036909 := by
  unfold tailWord_2237070
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199080750685615747958583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54395097336989950655779109 10199080750685615747958583)
  ·
    refine ⟨15298621126028423621937875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10199080750685615747958583 15298621126028423621937875)
    ·
      refine ⟨22947931689042635432906813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15298621126028423621937875 22947931689042635432906813)
      ·
        refine ⟨8605474383390988287340055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22947931689042635432906813 8605474383390988287340055)
        ·
          refine ⟨12908211575086482431010083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8605474383390988287340055 12908211575086482431010083)
          ·
            refine ⟨19362317362629723646515125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12908211575086482431010083 19362317362629723646515125)
            ·
              refine ⟨1815217252746536591860793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19362317362629723646515125 1815217252746536591860793)
              ·
                refine ⟨1361412939559902443895595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815217252746536591860793 1361412939559902443895595)
                ·
                  refine ⟨2042119409339853665843393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361412939559902443895595 2042119409339853665843393)
                  ·
                    refine ⟨1531589557004890249382545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2042119409339853665843393 1531589557004890249382545)
                    ·
                      refine ⟨1148692167753667687036909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531589557004890249382545 1148692167753667687036909)
                      ·
                        rfl

theorem cell23_2237070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2237070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237070 prefixEnd_2237070 := by exact prefixLift 2237070
  have htrace : WordTrace (prefixWord ++ tailWord_2237070) baseStart_2237070 baseEnd_2237070 := by
    simpa [prefixWord, tailWord_2237070, baseEnd_2237070] using wordTrace_append hprefix tailTrace_2237070
  have hstable : (prefixWord ++ tailWord_2237070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237070).length < 2 ^ (prefixWord ++ tailWord_2237070).sum := by decide
  have hdescent : baseEnd_2237070 < baseStart_2237070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237075 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4]
def baseStart_2237075 : Nat := 118140960795 + 2237075 * 2 ^ 59
def prefixEnd_2237075 : Nat := 4983230072969 + 3 ^ 40 * 2237075 * 2
def baseEnd_2237075 : Nat := 1148694735156940167474385

theorem tailTrace_2237075 : CollatzResearch.WordTrace tailWord_2237075 prefixEnd_2237075 1148694735156940167474385 := by
  unfold tailWord_2237075
  simp only [CollatzResearch.WordTrace]
  refine ⟨81592828370466811837600679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54395218913644541225067119 81592828370466811837600679)
  ·
    refine ⟨122389242555700217756401019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81592828370466811837600679 122389242555700217756401019)
    ·
      refine ⟨183583863833550326634601529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122389242555700217756401019 183583863833550326634601529)
      ·
        refine ⟨137687897875162744975951147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183583863833550326634601529 137687897875162744975951147)
        ·
          refine ⟨206531846812744117463926721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137687897875162744975951147 206531846812744117463926721)
          ·
            refine ⟨154898885109558088097945041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206531846812744117463926721 154898885109558088097945041)
            ·
              refine ⟨116174163832168566073458781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154898885109558088097945041 116174163832168566073458781)
              ·
                refine ⟨43565311437063212277547043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116174163832168566073458781 43565311437063212277547043)
                ·
                  refine ⟨65347967155594818416320565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43565311437063212277547043 65347967155594818416320565)
                  ·
                    refine ⟨6126371920837014226530053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65347967155594818416320565 6126371920837014226530053)
                    ·
                      refine ⟨1148694735156940167474385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6126371920837014226530053 1148694735156940167474385)
                      ·
                        rfl

theorem cell23_2237075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_2237075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237075 prefixEnd_2237075 := by exact prefixLift 2237075
  have htrace : WordTrace (prefixWord ++ tailWord_2237075) baseStart_2237075 baseEnd_2237075 := by
    simpa [prefixWord, tailWord_2237075, baseEnd_2237075] using wordTrace_append hprefix tailTrace_2237075
  have hstable : (prefixWord ++ tailWord_2237075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237075).length < 2 ^ (prefixWord ++ tailWord_2237075).sum := by decide
  have hdescent : baseEnd_2237075 < baseStart_2237075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237079 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 3, 3, 2]
def baseStart_2237079 : Nat := 118140960795 + 2237079 * 2 ^ 59
def prefixEnd_2237079 : Nat := 4983230072969 + 3 ^ 40 * 2237079 * 2
def baseEnd_2237079 : Nat := 1148696789079558151824367

theorem tailTrace_2237079 : CollatzResearch.WordTrace tailWord_2237079 prefixEnd_2237079 1148696789079558151824367 := by
  unfold tailWord_2237079
  simp only [CollatzResearch.WordTrace]
  refine ⟨81592974262452320520746291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54395316174968213680497527 81592974262452320520746291)
  ·
    refine ⟨122389461393678480781119437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81592974262452320520746291 122389461393678480781119437)
    ·
      refine ⟨45896048022629430292919789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122389461393678480781119437 45896048022629430292919789)
      ·
        refine ⟨17211018008486036359844921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45896048022629430292919789 17211018008486036359844921)
        ·
          refine ⟨12908263506364527269883691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17211018008486036359844921 12908263506364527269883691)
          ·
            refine ⟨19362395259546790904825537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12908263506364527269883691 19362395259546790904825537)
            ·
              refine ⟨14521796444660093178619153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19362395259546790904825537 14521796444660093178619153)
              ·
                refine ⟨10891347333495069883964365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14521796444660093178619153 10891347333495069883964365)
                ·
                  refine ⟨4084255250060651206486637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10891347333495069883964365 4084255250060651206486637)
                  ·
                    refine ⟨1531595718772744202432489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4084255250060651206486637 1531595718772744202432489)
                    ·
                      refine ⟨1148696789079558151824367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531595718772744202432489 1148696789079558151824367)
                      ·
                        rfl

theorem cell23_2237079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_2237079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237079 prefixEnd_2237079 := by exact prefixLift 2237079
  have htrace : WordTrace (prefixWord ++ tailWord_2237079) baseStart_2237079 baseEnd_2237079 := by
    simpa [prefixWord, tailWord_2237079, baseEnd_2237079] using wordTrace_append hprefix tailTrace_2237079
  have hstable : (prefixWord ++ tailWord_2237079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237079).length < 2 ^ (prefixWord ++ tailWord_2237079).sum := by decide
  have hdescent : baseEnd_2237079 < baseStart_2237079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237121 : List Nat := [1, 2, 6, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2237121 : Nat := 118140960795 + 2237121 * 2 ^ 59
def prefixEnd_2237121 : Nat := 4983230072969 + 3 ^ 40 * 2237121 * 2
def baseEnd_2237121 : Nat := 1148718355267046987499175

theorem tailTrace_2237121 : CollatzResearch.WordTrace tailWord_2237121 prefixEnd_2237121 1148718355267046987499175 := by
  unfold tailWord_2237121
  simp only [CollatzResearch.WordTrace]
  refine ⟨81594506128300161693775217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54396337418866774462516811 81594506128300161693775217)
  ·
    refine ⟨61195879596225121270331413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81594506128300161693775217 61195879596225121270331413)
    ·
      refine ⟨2868556856073052559546785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61195879596225121270331413 2868556856073052559546785)
      ·
        refine ⟨2151417642054789419660089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2868556856073052559546785 2151417642054789419660089)
        ·
          refine ⟨1613563231541092064745067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151417642054789419660089 1613563231541092064745067)
          ·
            refine ⟨2420344847311638097117601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613563231541092064745067 2420344847311638097117601)
            ·
              refine ⟨1815258635483728572838201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420344847311638097117601 1815258635483728572838201)
              ·
                refine ⟨1361443976612796429628651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815258635483728572838201 1361443976612796429628651)
                ·
                  refine ⟨2042165964919194644442977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361443976612796429628651 2042165964919194644442977)
                  ·
                    refine ⟨1531624473689395983332233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2042165964919194644442977 1531624473689395983332233)
                    ·
                      refine ⟨1148718355267046987499175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531624473689395983332233 1148718355267046987499175)
                      ·
                        rfl

theorem cell23_2237121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2237121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237121 prefixEnd_2237121 := by exact prefixLift 2237121
  have htrace : WordTrace (prefixWord ++ tailWord_2237121) baseStart_2237121 baseEnd_2237121 := by
    simpa [prefixWord, tailWord_2237121, baseEnd_2237121] using wordTrace_append hprefix tailTrace_2237121
  have hstable : (prefixWord ++ tailWord_2237121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237121).length < 2 ^ (prefixWord ++ tailWord_2237121).sum := by decide
  have hdescent : baseEnd_2237121 < baseStart_2237121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237135 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_2237135 : Nat := 118140960795 + 2237135 * 2 ^ 59
def prefixEnd_2237135 : Nat := 4983230072969 + 3 ^ 40 * 2237135 * 2
def baseEnd_2237135 : Nat := 1148725543996209932724109

theorem tailTrace_2237135 : CollatzResearch.WordTrace tailWord_2237135 prefixEnd_2237135 1148725543996209932724109 := by
  unfold tailWord_2237135
  simp only [CollatzResearch.WordTrace]
  refine ⟨81595016750249442084784859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54396677833499628056523239 81595016750249442084784859)
  ·
    refine ⟨122392525125374163127177289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81595016750249442084784859 122392525125374163127177289)
    ·
      refine ⟨91794393844030622345382967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122392525125374163127177289 91794393844030622345382967)
      ·
        refine ⟨137691590766045933518074451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91794393844030622345382967 137691590766045933518074451)
        ·
          refine ⟨206537386149068900277111677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137691590766045933518074451 206537386149068900277111677)
          ·
            refine ⟨77451519805900837603916879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206537386149068900277111677 77451519805900837603916879)
            ·
              refine ⟨116177279708851256405875319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77451519805900837603916879 116177279708851256405875319)
              ·
                refine ⟨174265919563276884608812979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116177279708851256405875319 174265919563276884608812979)
                ·
                  refine ⟨261398879344915326913219469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174265919563276884608812979 261398879344915326913219469)
                  ·
                    refine ⟨98024579754343247592457301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261398879344915326913219469 98024579754343247592457301)
                    ·
                      refine ⟨1148725543996209932724109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 98024579754343247592457301 1148725543996209932724109)
                      ·
                        rfl

theorem cell23_2237135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_2237135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237135 prefixEnd_2237135 := by exact prefixLift 2237135
  have htrace : WordTrace (prefixWord ++ tailWord_2237135) baseStart_2237135 baseEnd_2237135 := by
    simpa [prefixWord, tailWord_2237135, baseEnd_2237135] using wordTrace_append hprefix tailTrace_2237135
  have hstable : (prefixWord ++ tailWord_2237135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237135).length < 2 ^ (prefixWord ++ tailWord_2237135).sum := by decide
  have hdescent : baseEnd_2237135 < baseStart_2237135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237166 : List Nat := [4, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_2237166 : Nat := 118140960795 + 2237166 * 2 ^ 59
def prefixEnd_2237166 : Nat := 4983230072969 + 3 ^ 40 * 2237166 * 2
def baseEnd_2237166 : Nat := 127637940210722145715163

theorem tailTrace_2237166 : CollatzResearch.WordTrace tailWord_2237166 prefixEnd_2237166 127637940210722145715163 := by
  unfold tailWord_2237166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199518426642141797395419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54397431608758089586108901 10199518426642141797395419)
  ·
    refine ⟨15299277639963212696093129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10199518426642141797395419 15299277639963212696093129)
    ·
      refine ⟨11474458229972409522069847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15299277639963212696093129 11474458229972409522069847)
      ·
        refine ⟨17211687344958614283104771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11474458229972409522069847 17211687344958614283104771)
        ·
          refine ⟨25817531017437921424657157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17211687344958614283104771 25817531017437921424657157)
          ·
            refine ⟨4840787065769610267123217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25817531017437921424657157 4840787065769610267123217)
            ·
              refine ⟨3630590299327207700342413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4840787065769610267123217 3630590299327207700342413)
              ·
                refine ⟨1361471362247702887628405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3630590299327207700342413 1361471362247702887628405)
                ·
                  refine ⟨127637940210722145715163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1361471362247702887628405 127637940210722145715163)
                  ·
                    rfl

theorem cell23_2237166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_2237166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237166 prefixEnd_2237166 := by exact prefixLift 2237166
  have htrace : WordTrace (prefixWord ++ tailWord_2237166) baseStart_2237166 baseEnd_2237166 := by
    simpa [prefixWord, tailWord_2237166, baseEnd_2237166] using wordTrace_append hprefix tailTrace_2237166
  have hstable : (prefixWord ++ tailWord_2237166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237166).length < 2 ^ (prefixWord ++ tailWord_2237166).sum := by decide
  have hdescent : baseEnd_2237166 < baseStart_2237166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237199 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 2, 4, 2]
def baseStart_2237199 : Nat := 118140960795 + 2237199 * 2 ^ 59
def prefixEnd_2237199 : Nat := 4983230072969 + 3 ^ 40 * 2237199 * 2
def baseEnd_2237199 : Nat := 1148758406758097682323815

theorem tailTrace_2237199 : CollatzResearch.WordTrace tailWord_2237199 prefixEnd_2237199 1148758406758097682323815 := by
  unfold tailWord_2237199
  simp only [CollatzResearch.WordTrace]
  refine ⟨81597351022017581015114651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54398234014678387343409767 81597351022017581015114651)
  ·
    refine ⟨122396026533026371522671977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81597351022017581015114651 122396026533026371522671977)
    ·
      refine ⟨91797019899769778642003983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122396026533026371522671977 91797019899769778642003983)
      ·
        refine ⟨137695529849654667963005975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91797019899769778642003983 137695529849654667963005975)
        ·
          refine ⟨206543294774482001944508963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137695529849654667963005975 206543294774482001944508963)
          ·
            refine ⟨309814942161723002916763445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206543294774482001944508963 309814942161723002916763445)
            ·
              refine ⟨29045150827661531523446573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 309814942161723002916763445 29045150827661531523446573)
              ·
                refine ⟨10891931560373074321292465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29045150827661531523446573 10891931560373074321292465)
                ·
                  refine ⟨8168948670279805740969349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10891931560373074321292465 8168948670279805740969349)
                  ·
                    refine ⟨1531677875677463576431753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8168948670279805740969349 1531677875677463576431753)
                    ·
                      refine ⟨1148758406758097682323815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531677875677463576431753 1148758406758097682323815)
                      ·
                        rfl

theorem cell23_2237199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4, 2].length) (baseStart_2237199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237199 prefixEnd_2237199 := by exact prefixLift 2237199
  have htrace : WordTrace (prefixWord ++ tailWord_2237199) baseStart_2237199 baseEnd_2237199 := by
    simpa [prefixWord, tailWord_2237199, baseEnd_2237199] using wordTrace_append hprefix tailTrace_2237199
  have hstable : (prefixWord ++ tailWord_2237199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237199).length < 2 ^ (prefixWord ++ tailWord_2237199).sum := by decide
  have hdescent : baseEnd_2237199 < baseStart_2237199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237219 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 3]
def baseStart_2237219 : Nat := 118140960795 + 2237219 * 2 ^ 59
def prefixEnd_2237219 : Nat := 4983230072969 + 3 ^ 40 * 2237219 * 2
def baseEnd_2237219 : Nat := 1148768676371187604073723

theorem tailTrace_2237219 : CollatzResearch.WordTrace tailWord_2237219 prefixEnd_2237219 1148768676371187604073723 := by
  unfold tailWord_2237219
  simp only [CollatzResearch.WordTrace]
  refine ⟨81598080481945124430842711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54398720321296749620561807 81598080481945124430842711)
  ·
    refine ⟨122397120722917686646264067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81598080481945124430842711 122397120722917686646264067)
    ·
      refine ⟨183595681084376529969396101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122397120722917686646264067 183595681084376529969396101)
      ·
        refine ⟨34424190203320599369261769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183595681084376529969396101 34424190203320599369261769)
        ·
          refine ⟨25818142652490449526946327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34424190203320599369261769 25818142652490449526946327)
          ·
            refine ⟨38727213978735674290419491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25818142652490449526946327 38727213978735674290419491)
            ·
              refine ⟨58090820968103511435629237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38727213978735674290419491 58090820968103511435629237)
              ·
                refine ⟨5446014465759704197090241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58090820968103511435629237 5446014465759704197090241)
                ·
                  refine ⟨4084510849319778147817681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5446014465759704197090241 4084510849319778147817681)
                  ·
                    refine ⟨3063383136989833610863261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084510849319778147817681 3063383136989833610863261)
                    ·
                      refine ⟨1148768676371187604073723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3063383136989833610863261 1148768676371187604073723)
                      ·
                        rfl

theorem cell23_2237219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_2237219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237219 prefixEnd_2237219 := by exact prefixLift 2237219
  have htrace : WordTrace (prefixWord ++ tailWord_2237219) baseStart_2237219 baseEnd_2237219 := by
    simpa [prefixWord, tailWord_2237219, baseEnd_2237219] using wordTrace_append hprefix tailTrace_2237219
  have hstable : (prefixWord ++ tailWord_2237219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237219).length < 2 ^ (prefixWord ++ tailWord_2237219).sum := by decide
  have hdescent : baseEnd_2237219 < baseStart_2237219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237266 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_2237266 : Nat := 118140960795 + 2237266 * 2 ^ 59
def prefixEnd_2237266 : Nat := 4983230072969 + 3 ^ 40 * 2237266 * 2
def baseEnd_2237266 : Nat := 1148792809961948920186007

theorem tailTrace_2237266 : CollatzResearch.WordTrace tailWord_2237266 prefixEnd_2237266 1148792809961948920186007 := by
  unfold tailWord_2237266
  simp only [CollatzResearch.WordTrace]
  refine ⟨20399948678193712864450913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54399863141849900971869101 20399948678193712864450913)
  ·
    refine ⟨15299961508645284648338185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20399948678193712864450913 15299961508645284648338185)
    ·
      refine ⟨11474971131483963486253639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15299961508645284648338185 11474971131483963486253639)
      ·
        refine ⟨17212456697225945229380459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11474971131483963486253639 17212456697225945229380459)
        ·
          refine ⟨25818685045838917844070689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17212456697225945229380459 25818685045838917844070689)
          ·
            refine ⟨19364013784379188383053017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25818685045838917844070689 19364013784379188383053017)
            ·
              refine ⟨14523010338284391287289763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19364013784379188383053017 14523010338284391287289763)
              ·
                refine ⟨21784515507426586930934645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14523010338284391287289763 21784515507426586930934645)
                ·
                  refine ⟨2042298328821242524775123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21784515507426586930934645 2042298328821242524775123)
                  ·
                    refine ⟨3063447493231863787162685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2042298328821242524775123 3063447493231863787162685)
                    ·
                      refine ⟨1148792809961948920186007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3063447493231863787162685 1148792809961948920186007)
                      ·
                        rfl

theorem cell23_2237266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_2237266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237266 prefixEnd_2237266 := by exact prefixLift 2237266
  have htrace : WordTrace (prefixWord ++ tailWord_2237266) baseStart_2237266 baseEnd_2237266 := by
    simpa [prefixWord, tailWord_2237266, baseEnd_2237266] using wordTrace_append hprefix tailTrace_2237266
  have hstable : (prefixWord ++ tailWord_2237266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237266).length < 2 ^ (prefixWord ++ tailWord_2237266).sum := by decide
  have hdescent : baseEnd_2237266 < baseStart_2237266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237269 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2237269 : Nat := 118140960795 + 2237269 * 2 ^ 59
def prefixEnd_2237269 : Nat := 4983230072969 + 3 ^ 40 * 2237269 * 2
def baseEnd_2237269 : Nat := 382931450134637469482831

theorem tailTrace_2237269 : CollatzResearch.WordTrace tailWord_2237269 prefixEnd_2237269 382931450134637469482831 := by
  unfold tailWord_2237269
  simp only [CollatzResearch.WordTrace]
  refine ⟨81599904131763982970162861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54399936087842655313441907 81599904131763982970162861)
  ·
    refine ⟨30599964049411493613811073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81599904131763982970162861 30599964049411493613811073)
    ·
      refine ⟨22949973037058620210358305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30599964049411493613811073 22949973037058620210358305)
      ·
        refine ⟨17212479777793965157768729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22949973037058620210358305 17212479777793965157768729)
        ·
          refine ⟨12909359833345473868326547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17212479777793965157768729 12909359833345473868326547)
          ·
            refine ⟨19364039750018210802489821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12909359833345473868326547 19364039750018210802489821)
            ·
              refine ⟨7261514906256829050933683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19364039750018210802489821 7261514906256829050933683)
              ·
                refine ⟨10892272359385243576400525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7261514906256829050933683 10892272359385243576400525)
                ·
                  refine ⟨4084602134769466341150197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10892272359385243576400525 4084602134769466341150197)
                  ·
                    refine ⟨382931450134637469482831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4084602134769466341150197 382931450134637469482831)
                    ·
                      rfl

theorem cell23_2237269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2237269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237269 prefixEnd_2237269 := by exact prefixLift 2237269
  have htrace : WordTrace (prefixWord ++ tailWord_2237269) baseStart_2237269 baseEnd_2237269 := by
    simpa [prefixWord, tailWord_2237269, baseEnd_2237269] using wordTrace_append hprefix tailTrace_2237269
  have hstable : (prefixWord ++ tailWord_2237269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237269).length < 2 ^ (prefixWord ++ tailWord_2237269).sum := by decide
  have hdescent : baseEnd_2237269 < baseStart_2237269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237294 : List Nat := [4, 1, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2237294 : Nat := 118140960795 + 2237294 * 2 ^ 59
def prefixEnd_2237294 : Nat := 4983230072969 + 3 ^ 40 * 2237294 * 2
def baseEnd_2237294 : Nat := 382935729140091603545293

theorem tailTrace_2237294 : CollatzResearch.WordTrace tailWord_2237294 prefixEnd_2237294 382935729140091603545293 := by
  unfold tailWord_2237294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200101994584176529977867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54400543971115608159881957 10200101994584176529977867)
  ·
    refine ⟨15300152991876264794966801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200101994584176529977867 15300152991876264794966801)
    ·
      refine ⟨11475114743907198596225101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15300152991876264794966801 11475114743907198596225101)
      ·
        refine ⟨4303168028965199473584413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11475114743907198596225101 4303168028965199473584413)
        ·
          refine ⟨1613688010861949802594155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4303168028965199473584413 1613688010861949802594155)
          ·
            refine ⟨2420532016292924703891233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613688010861949802594155 2420532016292924703891233)
            ·
              refine ⟨1815399012219693527918425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420532016292924703891233 1815399012219693527918425)
              ·
                refine ⟨1361549259164770145938819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815399012219693527918425 1361549259164770145938819)
                ·
                  refine ⟨2042323888747155218908229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361549259164770145938819 2042323888747155218908229)
                  ·
                    refine ⟨382935729140091603545293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042323888747155218908229 382935729140091603545293)
                    ·
                      rfl

theorem cell23_2237294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2237294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237294 prefixEnd_2237294 := by exact prefixLift 2237294
  have htrace : WordTrace (prefixWord ++ tailWord_2237294) baseStart_2237294 baseEnd_2237294 := by
    simpa [prefixWord, tailWord_2237294, baseEnd_2237294] using wordTrace_append hprefix tailTrace_2237294
  have hstable : (prefixWord ++ tailWord_2237294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237294).length < 2 ^ (prefixWord ++ tailWord_2237294).sum := by decide
  have hdescent : baseEnd_2237294 < baseStart_2237294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237299 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 4, 4]
def baseStart_2237299 : Nat := 118140960795 + 2237299 * 2 ^ 59
def prefixEnd_2237299 : Nat := 4983230072969 + 3 ^ 40 * 2237299 * 2
def baseEnd_2237299 : Nat := 382936584941182430357785

theorem tailTrace_2237299 : CollatzResearch.WordTrace tailWord_2237299 prefixEnd_2237299 382936584941182430357785 := by
  unfold tailWord_2237299
  simp only [CollatzResearch.WordTrace]
  refine ⟨81600998321655298093754951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54400665547770198729169967 81600998321655298093754951)
  ·
    refine ⟨122401497482482947140632427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81600998321655298093754951 122401497482482947140632427)
    ·
      refine ⟨183602246223724420710948641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122401497482482947140632427 183602246223724420710948641)
      ·
        refine ⟨137701684667793315533211481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183602246223724420710948641 137701684667793315533211481)
        ·
          refine ⟨103276263500844986649908611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137701684667793315533211481 103276263500844986649908611)
          ·
            refine ⟨154914395251267479974862917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103276263500844986649908611 154914395251267479974862917)
            ·
              refine ⟨29046449109612652495286797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154914395251267479974862917 29046449109612652495286797)
              ·
                refine ⟨10892418416104744685732549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29046449109612652495286797 10892418416104744685732549)
                ·
                  refine ⟨2042328453019639628574853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10892418416104744685732549 2042328453019639628574853)
                  ·
                    refine ⟨382936584941182430357785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042328453019639628574853 382936584941182430357785)
                    ·
                      rfl

theorem cell23_2237299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 4].length) (baseStart_2237299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237299 prefixEnd_2237299 := by exact prefixLift 2237299
  have htrace : WordTrace (prefixWord ++ tailWord_2237299) baseStart_2237299 baseEnd_2237299 := by
    simpa [prefixWord, tailWord_2237299, baseEnd_2237299] using wordTrace_append hprefix tailTrace_2237299
  have hstable : (prefixWord ++ tailWord_2237299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237299).length < 2 ^ (prefixWord ++ tailWord_2237299).sum := by decide
  have hdescent : baseEnd_2237299 < baseStart_2237299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237309 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_2237309 : Nat := 118140960795 + 2237309 * 2 ^ 59
def prefixEnd_2237309 : Nat := 4983230072969 + 3 ^ 40 * 2237309 * 2
def baseEnd_2237309 : Nat := 1148814889630092251948309

theorem tailTrace_2237309 : CollatzResearch.WordTrace tailWord_2237309 prefixEnd_2237309 1148814889630092251948309 := by
  unfold tailWord_2237309
  simp only [CollatzResearch.WordTrace]
  refine ⟨81601363051619069801618981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54400908701079379867745987 81601363051619069801618981)
  ·
    refine ⟨15300255572178575587803559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81601363051619069801618981 15300255572178575587803559)
    ·
      refine ⟨22950383358267863381705339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15300255572178575587803559 22950383358267863381705339)
      ·
        refine ⟨34425575037401795072558009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22950383358267863381705339 34425575037401795072558009)
        ·
          refine ⟨25819181278051346304418507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34425575037401795072558009 25819181278051346304418507)
          ·
            refine ⟨38728771917077019456627761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25819181278051346304418507 38728771917077019456627761)
            ·
              refine ⟨29046578937807764592470821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38728771917077019456627761 29046578937807764592470821)
              ·
                refine ⟨5446233550838955861088279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29046578937807764592470821 5446233550838955861088279)
                ·
                  refine ⟨8169350326258433791632419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446233550838955861088279 8169350326258433791632419)
                  ·
                    refine ⟨12254025489387650687448629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8169350326258433791632419 12254025489387650687448629)
                    ·
                      refine ⟨1148814889630092251948309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12254025489387650687448629 1148814889630092251948309)
                      ·
                        rfl

theorem cell23_2237309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_2237309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237309 prefixEnd_2237309 := by exact prefixLift 2237309
  have htrace : WordTrace (prefixWord ++ tailWord_2237309) baseStart_2237309 baseEnd_2237309 := by
    simpa [prefixWord, tailWord_2237309, baseEnd_2237309] using wordTrace_append hprefix tailTrace_2237309
  have hstable : (prefixWord ++ tailWord_2237309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237309).length < 2 ^ (prefixWord ++ tailWord_2237309).sum := by decide
  have hdescent : baseEnd_2237309 < baseStart_2237309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237312 : List Nat := [2, 1, 1, 2, 1, 2, 2, 12]
def baseStart_2237312 : Nat := 118140960795 + 2237312 * 2 ^ 59
def prefixEnd_2237312 : Nat := 4983230072969 + 3 ^ 40 * 2237312 * 2
def baseEnd_2237312 : Nat := 42548756669335397785585

theorem tailTrace_2237312 : CollatzResearch.WordTrace tailWord_2237312 prefixEnd_2237312 42548756669335397785585 := by
  unfold tailWord_2237312
  simp only [CollatzResearch.WordTrace]
  refine ⟨40800736235304100656989095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54400981647072134209318793 40800736235304100656989095)
  ·
    refine ⟨61201104352956150985483643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40800736235304100656989095 61201104352956150985483643)
    ·
      refine ⟨91801656529434226478225465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61201104352956150985483643 91801656529434226478225465)
      ·
        refine ⟨68851242397075669858669099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91801656529434226478225465 68851242397075669858669099)
        ·
          refine ⟨103276863595613504788003649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68851242397075669858669099 103276863595613504788003649)
          ·
            refine ⟨77457647696710128591002737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103276863595613504788003649 77457647696710128591002737)
            ·
              refine ⟨58093235772532596443252053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77457647696710128591002737 58093235772532596443252053)
              ·
                refine ⟨42548756669335397785585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 58093235772532596443252053 42548756669335397785585)
                ·
                  rfl

theorem cell23_2237312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 12].length) (baseStart_2237312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237312 prefixEnd_2237312 := by exact prefixLift 2237312
  have htrace : WordTrace (prefixWord ++ tailWord_2237312) baseStart_2237312 baseEnd_2237312 := by
    simpa [prefixWord, tailWord_2237312, baseEnd_2237312] using wordTrace_append hprefix tailTrace_2237312
  have hstable : (prefixWord ++ tailWord_2237312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237312).length < 2 ^ (prefixWord ++ tailWord_2237312).sum := by decide
  have hdescent : baseEnd_2237312 < baseStart_2237312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237334 : List Nat := [5, 3, 1, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2237334 : Nat := 118140960795 + 2237334 * 2 ^ 59
def prefixEnd_2237334 : Nat := 4983230072969 + 3 ^ 40 * 2237334 * 2
def baseEnd_2237334 : Nat := 1148827726646454654135695

theorem tailTrace_2237334 : CollatzResearch.WordTrace tailWord_2237334 prefixEnd_2237334 1148827726646454654135695 := by
  unfold tailWord_2237334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100142179783031191954941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54401516584352332714186037 5100142179783031191954941)
  ·
    refine ⟨1912553317418636696983103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5100142179783031191954941 1912553317418636696983103)
    ·
      refine ⟨2868829976127955045474655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912553317418636696983103 2868829976127955045474655)
      ·
        refine ⟨4303244964191932568211983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868829976127955045474655 4303244964191932568211983)
        ·
          refine ⟨6454867446287898852317975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4303244964191932568211983 6454867446287898852317975)
          ·
            refine ⟨9682301169431848278476963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6454867446287898852317975 9682301169431848278476963)
            ·
              refine ⟨14523451754147772417715445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9682301169431848278476963 14523451754147772417715445)
              ·
                refine ⟨1361573601951353664160823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14523451754147772417715445 1361573601951353664160823)
                ·
                  refine ⟨2042360402927030496241235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361573601951353664160823 2042360402927030496241235)
                  ·
                    refine ⟨3063540604390545744361853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2042360402927030496241235 3063540604390545744361853)
                    ·
                      refine ⟨1148827726646454654135695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3063540604390545744361853 1148827726646454654135695)
                      ·
                        rfl

theorem cell23_2237334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2237334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237334 prefixEnd_2237334 := by exact prefixLift 2237334
  have htrace : WordTrace (prefixWord ++ tailWord_2237334) baseStart_2237334 baseEnd_2237334 := by
    simpa [prefixWord, tailWord_2237334, baseEnd_2237334] using wordTrace_append hprefix tailTrace_2237334
  have hstable : (prefixWord ++ tailWord_2237334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237334).length < 2 ^ (prefixWord ++ tailWord_2237334).sum := by decide
  have hdescent : baseEnd_2237334 < baseStart_2237334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237343 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2237343 : Nat := 118140960795 + 2237343 * 2 ^ 59
def prefixEnd_2237343 : Nat := 4983230072969 + 3 ^ 40 * 2237343 * 2
def baseEnd_2237343 : Nat := 1148832347972345118923153

theorem tailTrace_2237343 : CollatzResearch.WordTrace tailWord_2237343 prefixEnd_2237343 1148832347972345118923153 := by
  unfold tailWord_2237343
  simp only [CollatzResearch.WordTrace]
  refine ⟨81602603133495893608356683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54401735422330595738904455 81602603133495893608356683)
  ·
    refine ⟨122403904700243840412535025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81602603133495893608356683 122403904700243840412535025)
    ·
      refine ⟨91802928525182880309401269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122403904700243840412535025 91802928525182880309401269)
      ·
        refine ⟨8606524549235895029006369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91802928525182880309401269 8606524549235895029006369)
        ·
          refine ⟨6454893411926921271754777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8606524549235895029006369 6454893411926921271754777)
          ·
            refine ⟨4841170058945190953816083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6454893411926921271754777 4841170058945190953816083)
            ·
              refine ⟨7261755088417786430724125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4841170058945190953816083 7261755088417786430724125)
              ·
                refine ⟨2723158158156669911521547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7261755088417786430724125 2723158158156669911521547)
                ·
                  refine ⟨4084737237235004867282321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723158158156669911521547 4084737237235004867282321)
                  ·
                    refine ⟨3063552927926253650461741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084737237235004867282321 3063552927926253650461741)
                    ·
                      refine ⟨1148832347972345118923153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3063552927926253650461741 1148832347972345118923153)
                      ·
                        rfl

theorem cell23_2237343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2237343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237343 prefixEnd_2237343 := by exact prefixLift 2237343
  have htrace : WordTrace (prefixWord ++ tailWord_2237343) baseStart_2237343 baseEnd_2237343 := by
    simpa [prefixWord, tailWord_2237343, baseEnd_2237343] using wordTrace_append hprefix tailTrace_2237343
  have hstable : (prefixWord ++ tailWord_2237343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237343).length < 2 ^ (prefixWord ++ tailWord_2237343).sum := by decide
  have hdescent : baseEnd_2237343 < baseStart_2237343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237356 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_2237356 : Nat := 118140960795 + 2237356 * 2 ^ 59
def prefixEnd_2237356 : Nat := 4983230072969 + 3 ^ 40 * 2237356 * 2
def baseEnd_2237356 : Nat := 1148839023220853568060593

theorem tailTrace_2237356 : CollatzResearch.WordTrace tailWord_2237356 prefixEnd_2237356 1148839023220853568060593 := by
  unfold tailWord_2237356
  simp only [CollatzResearch.WordTrace]
  refine ⟨40801538641224398414289961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54402051521632531219053281 40801538641224398414289961)
  ·
    refine ⟨30601153980918298810717471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40801538641224398414289961 30601153980918298810717471)
    ·
      refine ⟨45901730971377448216076207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30601153980918298810717471 45901730971377448216076207)
      ·
        refine ⟨68852596457066172324114311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45901730971377448216076207 68852596457066172324114311)
        ·
          refine ⟨103278894685599258486171467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68852596457066172324114311 103278894685599258486171467)
          ·
            refine ⟨154918342028398887729257201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103278894685599258486171467 154918342028398887729257201)
            ·
              refine ⟨116188756521299165796942901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154918342028398887729257201 116188756521299165796942901)
              ·
                refine ⟨10892695923871796793463397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116188756521299165796942901 10892695923871796793463397)
                ·
                  refine ⟨2042380485725961898774387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10892695923871796793463397 2042380485725961898774387)
                  ·
                    refine ⟨3063570728588942848161581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2042380485725961898774387 3063570728588942848161581)
                    ·
                      refine ⟨1148839023220853568060593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3063570728588942848161581 1148839023220853568060593)
                      ·
                        rfl

theorem cell23_2237356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_2237356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237356 prefixEnd_2237356 := by exact prefixLift 2237356
  have htrace : WordTrace (prefixWord ++ tailWord_2237356) baseStart_2237356 baseEnd_2237356 := by
    simpa [prefixWord, tailWord_2237356, baseEnd_2237356] using wordTrace_append hprefix tailTrace_2237356
  have hstable : (prefixWord ++ tailWord_2237356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237356).length < 2 ^ (prefixWord ++ tailWord_2237356).sum := by decide
  have hdescent : baseEnd_2237356 < baseStart_2237356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237380 : List Nat := [2, 3, 3, 3, 1, 2, 2, 7]
def baseStart_2237380 : Nat := 118140960795 + 2237380 * 2 ^ 59
def prefixEnd_2237380 : Nat := 4983230072969 + 3 ^ 40 * 2237380 * 2
def baseEnd_2237380 : Nat := 42550049879872647191129

theorem tailTrace_2237380 : CollatzResearch.WordTrace tailWord_2237380 prefixEnd_2237380 42550049879872647191129 := by
  unfold tailWord_2237380
  simp only [CollatzResearch.WordTrace]
  refine ⟨40801976317180924463726797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54402635089574565951635729 40801976317180924463726797)
  ·
    refine ⟨15300741118942846673897549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40801976317180924463726797 15300741118942846673897549)
    ·
      refine ⟨5737777919603567502711581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15300741118942846673897549 5737777919603567502711581)
      ·
        refine ⟨2151666719851337813516843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5737777919603567502711581 2151666719851337813516843)
        ·
          refine ⟨3227500079777006720275265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151666719851337813516843 3227500079777006720275265)
          ·
            refine ⟨2420625059832755040206449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3227500079777006720275265 2420625059832755040206449)
            ·
              refine ⟨1815468794874566280154837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420625059832755040206449 1815468794874566280154837)
              ·
                refine ⟨42550049879872647191129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1815468794874566280154837 42550049879872647191129)
                ·
                  rfl

theorem cell23_2237380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 7].length) (baseStart_2237380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237380 prefixEnd_2237380 := by exact prefixLift 2237380
  have htrace : WordTrace (prefixWord ++ tailWord_2237380) baseStart_2237380 baseEnd_2237380 := by
    simpa [prefixWord, tailWord_2237380, baseEnd_2237380] using wordTrace_append hprefix tailTrace_2237380
  have hstable : (prefixWord ++ tailWord_2237380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237380).length < 2 ^ (prefixWord ++ tailWord_2237380).sum := by decide
  have hdescent : baseEnd_2237380 < baseStart_2237380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237383 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_2237383 : Nat := 118140960795 + 2237383 * 2 ^ 59
def prefixEnd_2237383 : Nat := 4983230072969 + 3 ^ 40 * 2237383 * 2
def baseEnd_2237383 : Nat := 1148852887198524962422969

theorem tailTrace_2237383 : CollatzResearch.WordTrace tailWord_2237383 prefixEnd_2237383 1148852887198524962422969 := by
  unfold tailWord_2237383
  simp only [CollatzResearch.WordTrace]
  refine ⟨81604062053350980439812803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54402708035567320293208535 81604062053350980439812803)
  ·
    refine ⟨122406093080026470659719205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81604062053350980439812803 122406093080026470659719205)
    ·
      refine ⟨22951142452504963248697351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122406093080026470659719205 22951142452504963248697351)
      ·
        refine ⟨34426713678757444873046027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22951142452504963248697351 34426713678757444873046027)
        ·
          refine ⟨51640070518136167309569041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34426713678757444873046027 51640070518136167309569041)
          ·
            refine ⟨38730052888602125482176781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51640070518136167309569041 38730052888602125482176781)
            ·
              refine ⟨14523769833225797055816293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38730052888602125482176781 14523769833225797055816293)
              ·
                refine ⟨2723206843729836947965555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14523769833225797055816293 2723206843729836947965555)
                ·
                  refine ⟨4084810265594755421948333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723206843729836947965555 4084810265594755421948333)
                  ·
                    refine ⟨1531803849598033283230625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4084810265594755421948333 1531803849598033283230625)
                    ·
                      refine ⟨1148852887198524962422969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531803849598033283230625 1148852887198524962422969)
                      ·
                        rfl

theorem cell23_2237383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_2237383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237383 prefixEnd_2237383 := by exact prefixLift 2237383
  have htrace : WordTrace (prefixWord ++ tailWord_2237383) baseStart_2237383 baseEnd_2237383 := by
    simpa [prefixWord, tailWord_2237383, baseEnd_2237383] using wordTrace_append hprefix tailTrace_2237383
  have hstable : (prefixWord ++ tailWord_2237383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237383).length < 2 ^ (prefixWord ++ tailWord_2237383).sum := by decide
  have hdescent : baseEnd_2237383 < baseStart_2237383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237428 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2237428 : Nat := 118140960795 + 2237428 * 2 ^ 59
def prefixEnd_2237428 : Nat := 4983230072969 + 3 ^ 40 * 2237428 * 2
def baseEnd_2237428 : Nat := 1148875993827977286360263

theorem tailTrace_2237428 : CollatzResearch.WordTrace tailWord_2237428 prefixEnd_2237428 1148875993827977286360263 := by
  unfold tailWord_2237428
  simp only [CollatzResearch.WordTrace]
  refine ⟨40802851669093976562600469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54403802225458635416800625 40802851669093976562600469)
  ·
    refine ⟨1912633671988780151371897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40802851669093976562600469 1912633671988780151371897)
    ·
      refine ⟨1434475253991585113528923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1912633671988780151371897 1434475253991585113528923)
      ·
        refine ⟨2151712880987377670293385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434475253991585113528923 2151712880987377670293385)
        ·
          refine ⟨1613784660740533252720039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151712880987377670293385 1613784660740533252720039)
          ·
            refine ⟨2420676991110799879080059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613784660740533252720039 2420676991110799879080059)
            ·
              refine ⟨3631015486666199818620089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420676991110799879080059 3631015486666199818620089)
              ·
                refine ⟨2723261614999649863965067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3631015486666199818620089 2723261614999649863965067)
                ·
                  refine ⟨4084892422499474795947601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723261614999649863965067 4084892422499474795947601)
                  ·
                    refine ⟨3063669316874606096960701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084892422499474795947601 3063669316874606096960701)
                    ·
                      refine ⟨1148875993827977286360263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3063669316874606096960701 1148875993827977286360263)
                      ·
                        rfl

theorem cell23_2237428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2237428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237428 prefixEnd_2237428 := by exact prefixLift 2237428
  have htrace : WordTrace (prefixWord ++ tailWord_2237428) baseStart_2237428 baseEnd_2237428 := by
    simpa [prefixWord, tailWord_2237428, baseEnd_2237428] using wordTrace_append hprefix tailTrace_2237428
  have hstable : (prefixWord ++ tailWord_2237428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237428).length < 2 ^ (prefixWord ++ tailWord_2237428).sum := by decide
  have hdescent : baseEnd_2237428 < baseStart_2237428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237449 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 1, 7]
def baseStart_2237449 : Nat := 118140960795 + 2237449 * 2 ^ 59
def prefixEnd_2237449 : Nat := 4983230072969 + 3 ^ 40 * 2237449 * 2
def baseEnd_2237449 : Nat := 382962258973907234732555

theorem tailTrace_2237449 : CollatzResearch.WordTrace tailWord_2237449 prefixEnd_2237449 382962258973907234732555 := by
  unfold tailWord_2237449
  simp only [CollatzResearch.WordTrace]
  refine ⟨81606469271111873711715401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54404312847407915807810267 81606469271111873711715401)
  ·
    refine ⟨61204851953333905283786551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81606469271111873711715401 61204851953333905283786551)
    ·
      refine ⟨91807277930000857925679827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61204851953333905283786551 91807277930000857925679827)
      ·
        refine ⟨137710916895001286888519741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91807277930000857925679827 137710916895001286888519741)
        ·
          refine ⟨51641593835625482583194903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137710916895001286888519741 51641593835625482583194903)
          ·
            refine ⟨77462390753438223874792355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51641593835625482583194903 77462390753438223874792355)
            ·
              refine ⟨116193586130157335812188533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77462390753438223874792355 116193586130157335812188533)
              ·
                refine ⟨10893148699702250232392675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116193586130157335812188533 10893148699702250232392675)
                ·
                  refine ⟨16339723049553375348589013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10893148699702250232392675 16339723049553375348589013)
                  ·
                    refine ⟨382962258973907234732555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16339723049553375348589013 382962258973907234732555)
                    ·
                      rfl

theorem cell23_2237449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_2237449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237449 prefixEnd_2237449 := by exact prefixLift 2237449
  have htrace : WordTrace (prefixWord ++ tailWord_2237449) baseStart_2237449 baseEnd_2237449 := by
    simpa [prefixWord, tailWord_2237449, baseEnd_2237449] using wordTrace_append hprefix tailTrace_2237449
  have hstable : (prefixWord ++ tailWord_2237449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237449).length < 2 ^ (prefixWord ++ tailWord_2237449).sum := by decide
  have hdescent : baseEnd_2237449 < baseStart_2237449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237456 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 7, 2]
def baseStart_2237456 : Nat := 118140960795 + 2237456 * 2 ^ 59
def prefixEnd_2237456 : Nat := 4983230072969 + 3 ^ 40 * 2237456 * 2
def baseEnd_2237456 : Nat := 1148890371286303176810133

theorem tailTrace_2237456 : CollatzResearch.WordTrace tailWord_2237456 prefixEnd_2237456 1148890371286303176810133 := by
  unfold tailWord_2237456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40803362291043256953610111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54404483054724342604813481 40803362291043256953610111)
  ·
    refine ⟨61205043436564885430415167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40803362291043256953610111 61205043436564885430415167)
    ·
      refine ⟨91807565154847328145622751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61205043436564885430415167 91807565154847328145622751)
      ·
        refine ⟨137711347732270992218434127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91807565154847328145622751 137711347732270992218434127)
        ·
          refine ⟨206567021598406488327651191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137711347732270992218434127 206567021598406488327651191)
          ·
            refine ⟨309850532397609732491476787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206567021598406488327651191 309850532397609732491476787)
            ·
              refine ⟨464775798596414598737215181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309850532397609732491476787 464775798596414598737215181)
              ·
                refine ⟨174290924473655474526455693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 464775798596414598737215181 174290924473655474526455693)
                ·
                  refine ⟨65359096677620802947420885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174290924473655474526455693 65359096677620802947420885)
                  ·
                    refine ⟨1531853828381737569080177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65359096677620802947420885 1531853828381737569080177)
                    ·
                      refine ⟨1148890371286303176810133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531853828381737569080177 1148890371286303176810133)
                      ·
                        rfl

theorem cell23_2237456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 7, 2].length) (baseStart_2237456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237456 prefixEnd_2237456 := by exact prefixLift 2237456
  have htrace : WordTrace (prefixWord ++ tailWord_2237456) baseStart_2237456 baseEnd_2237456 := by
    simpa [prefixWord, tailWord_2237456, baseEnd_2237456] using wordTrace_append hprefix tailTrace_2237456
  have hstable : (prefixWord ++ tailWord_2237456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237456).length < 2 ^ (prefixWord ++ tailWord_2237456).sum := by decide
  have hdescent : baseEnd_2237456 < baseStart_2237456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237466 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_2237466 : Nat := 118140960795 + 2237466 * 2 ^ 59
def prefixEnd_2237466 : Nat := 4983230072969 + 3 ^ 40 * 2237466 * 2
def baseEnd_2237466 : Nat := 382965168697616045895029

theorem tailTrace_2237466 : CollatzResearch.WordTrace tailWord_2237466 prefixEnd_2237466 382965168697616045895029 := by
  unfold tailWord_2237466
  simp only [CollatzResearch.WordTrace]
  refine ⟨20401772328012571403771063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54404726208033523743389501 20401772328012571403771063)
  ·
    refine ⟨30602658492018857105656595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20401772328012571403771063 30602658492018857105656595)
    ·
      refine ⟨45903987738028285658484893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30602658492018857105656595 45903987738028285658484893)
      ·
        refine ⟨17213995401760607121931835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45903987738028285658484893 17213995401760607121931835)
        ·
          refine ⟨25820993102640910682897753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17213995401760607121931835 25820993102640910682897753)
          ·
            refine ⟨19365744826980683012173315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25820993102640910682897753 19365744826980683012173315)
            ·
              refine ⟨29048617240471024518259973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19365744826980683012173315 29048617240471024518259973)
              ·
                refine ⟨5446615732588317097173745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29048617240471024518259973 5446615732588317097173745)
                ·
                  refine ⟨4084961799441237822880309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5446615732588317097173745 4084961799441237822880309)
                  ·
                    refine ⟨382965168697616045895029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4084961799441237822880309 382965168697616045895029)
                    ·
                      rfl

theorem cell23_2237466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_2237466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237466 prefixEnd_2237466 := by exact prefixLift 2237466
  have htrace : WordTrace (prefixWord ++ tailWord_2237466) baseStart_2237466 baseEnd_2237466 := by
    simpa [prefixWord, tailWord_2237466, baseEnd_2237466] using wordTrace_append hprefix tailTrace_2237466
  have hstable : (prefixWord ++ tailWord_2237466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237466).length < 2 ^ (prefixWord ++ tailWord_2237466).sum := by decide
  have hdescent : baseEnd_2237466 < baseStart_2237466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237473 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_2237473 : Nat := 118140960795 + 2237473 * 2 ^ 59
def prefixEnd_2237473 : Nat := 4983230072969 + 3 ^ 40 * 2237473 * 2
def baseEnd_2237473 : Nat := 1148899100457429610297555

theorem tailTrace_2237473 : CollatzResearch.WordTrace tailWord_2237473 prefixEnd_2237473 1148899100457429610297555 := by
  unfold tailWord_2237473
  simp only [CollatzResearch.WordTrace]
  refine ⟨81607344623024925810589073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54404896415349950540392715 81607344623024925810589073)
  ·
    refine ⟨61205508467268694357941805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81607344623024925810589073 61205508467268694357941805)
    ·
      refine ⟨22952065675225760384228177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61205508467268694357941805 22952065675225760384228177)
      ·
        refine ⟨17214049256419320288171133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22952065675225760384228177 17214049256419320288171133)
        ·
          refine ⟨6455268471157245108064175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17214049256419320288171133 6455268471157245108064175)
          ·
            refine ⟨9682902706735867662096263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455268471157245108064175 9682902706735867662096263)
            ·
              refine ⟨14524354060103801493144395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9682902706735867662096263 14524354060103801493144395)
              ·
                refine ⟨21786531090155702239716593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14524354060103801493144395 21786531090155702239716593)
                ·
                  refine ⟨16339898317616776679787445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21786531090155702239716593 16339898317616776679787445)
                  ·
                    refine ⟨1531865467276572813730073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16339898317616776679787445 1531865467276572813730073)
                    ·
                      refine ⟨1148899100457429610297555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531865467276572813730073 1148899100457429610297555)
                      ·
                        rfl

theorem cell23_2237473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_2237473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237473 prefixEnd_2237473 := by exact prefixLift 2237473
  have htrace : WordTrace (prefixWord ++ tailWord_2237473) baseStart_2237473 baseEnd_2237473 := by
    simpa [prefixWord, tailWord_2237473, baseEnd_2237473] using wordTrace_append hprefix tailTrace_2237473
  have hstable : (prefixWord ++ tailWord_2237473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237473).length < 2 ^ (prefixWord ++ tailWord_2237473).sum := by decide
  have hdescent : baseEnd_2237473 < baseStart_2237473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237499 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6]
def baseStart_2237499 : Nat := 118140960795 + 2237499 * 2 ^ 59
def prefixEnd_2237499 : Nat := 4983230072969 + 3 ^ 40 * 2237499 * 2
def baseEnd_2237499 : Nat := 1148912450954446508572435

theorem tailTrace_2237499 : CollatzResearch.WordTrace tailWord_2237499 prefixEnd_2237499 1148912450954446508572435 := by
  unfold tailWord_2237499
  simp only [CollatzResearch.WordTrace]
  refine ⟨81608292920930732251035551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54405528613953821500690367 81608292920930732251035551)
  ·
    refine ⟨122412439381396098376553327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81608292920930732251035551 122412439381396098376553327)
    ·
      refine ⟨183618659072094147564829991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122412439381396098376553327 183618659072094147564829991)
      ·
        refine ⟨275427988608141221347244987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183618659072094147564829991 275427988608141221347244987)
        ·
          refine ⟨413141982912211832020867481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275427988608141221347244987 413141982912211832020867481)
          ·
            refine ⟨309856487184158874015650611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413141982912211832020867481 309856487184158874015650611)
            ·
              refine ⟨464784730776238311023475917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309856487184158874015650611 464784730776238311023475917)
              ·
                refine ⟨174294274041089366633803469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 464784730776238311023475917 174294274041089366633803469)
                ·
                  refine ⟨65360352765408512487676301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174294274041089366633803469 65360352765408512487676301)
                  ·
                    refine ⟨24510132287028192182878613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65360352765408512487676301 24510132287028192182878613)
                    ·
                      refine ⟨1148912450954446508572435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24510132287028192182878613 1148912450954446508572435)
                      ·
                        rfl

theorem cell23_2237499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_2237499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237499 prefixEnd_2237499 := by exact prefixLift 2237499
  have htrace : WordTrace (prefixWord ++ tailWord_2237499) baseStart_2237499 baseEnd_2237499 := by
    simpa [prefixWord, tailWord_2237499, baseEnd_2237499] using wordTrace_append hprefix tailTrace_2237499
  have hstable : (prefixWord ++ tailWord_2237499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237499).length < 2 ^ (prefixWord ++ tailWord_2237499).sum := by decide
  have hdescent : baseEnd_2237499 < baseStart_2237499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237553 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_2237553 : Nat := 118140960795 + 2237553 * 2 ^ 59
def prefixEnd_2237553 : Nat := 4983230072969 + 3 ^ 40 * 2237553 * 2
def baseEnd_2237553 : Nat := 1148940178909789297297187

theorem tailTrace_2237553 : CollatzResearch.WordTrace tailWord_2237553 prefixEnd_2237553 1148940178909789297297187 := by
  unfold tailWord_2237553
  simp only [CollatzResearch.WordTrace]
  refine ⟨81610262462735099473501313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54406841641823399649000875 81610262462735099473501313)
  ·
    refine ⟨61207696847051324605125985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81610262462735099473501313 61207696847051324605125985)
    ·
      refine ⟨45905772635288493453844489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61207696847051324605125985 45905772635288493453844489)
      ·
        refine ⟨34429329476466370090383367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45905772635288493453844489 34429329476466370090383367)
        ·
          refine ⟨51643994214699555135575051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34429329476466370090383367 51643994214699555135575051)
          ·
            refine ⟨77465991322049332703362577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51643994214699555135575051 77465991322049332703362577)
            ·
              refine ⟨58099493491536999527521933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77465991322049332703362577 58099493491536999527521933)
              ·
                refine ⟨21787310059326374822820725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58099493491536999527521933 21787310059326374822820725)
                ·
                  refine ⟨2042560318061847639639443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21787310059326374822820725 2042560318061847639639443)
                  ·
                    refine ⟨3063840477092771459459165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2042560318061847639639443 3063840477092771459459165)
                    ·
                      refine ⟨1148940178909789297297187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3063840477092771459459165 1148940178909789297297187)
                      ·
                        rfl

theorem cell23_2237553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_2237553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237553 prefixEnd_2237553 := by exact prefixLift 2237553
  have htrace : WordTrace (prefixWord ++ tailWord_2237553) baseStart_2237553 baseEnd_2237553 := by
    simpa [prefixWord, tailWord_2237553, baseEnd_2237553] using wordTrace_append hprefix tailTrace_2237553
  have hstable : (prefixWord ++ tailWord_2237553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237553).length < 2 ^ (prefixWord ++ tailWord_2237553).sum := by decide
  have hdescent : baseEnd_2237553 < baseStart_2237553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237563 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 6, 3, 2]
def baseStart_2237563 : Nat := 118140960795 + 2237563 * 2 ^ 59
def prefixEnd_2237563 : Nat := 4983230072969 + 3 ^ 40 * 2237563 * 2
def baseEnd_2237563 : Nat := 1148945313716334258172141

theorem tailTrace_2237563 : CollatzResearch.WordTrace tailWord_2237563 prefixEnd_2237563 1148945313716334258172141 := by
  unfold tailWord_2237563
  simp only [CollatzResearch.WordTrace]
  refine ⟨81610627192698871181365343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54407084795132580787576895 81610627192698871181365343)
  ·
    refine ⟨122415940789048306772048015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81610627192698871181365343 122415940789048306772048015)
    ·
      refine ⟨183623911183572460158072023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122415940789048306772048015 183623911183572460158072023)
      ·
        refine ⟨275435866775358690237108035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183623911183572460158072023 275435866775358690237108035)
        ·
          refine ⟨413153800163038035355662053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275435866775358690237108035 413153800163038035355662053)
          ·
            refine ⟨77466337530569631629186635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 413153800163038035355662053 77466337530569631629186635)
            ·
              refine ⟨116199506295854447443779953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77466337530569631629186635 116199506295854447443779953)
              ·
                refine ⟨87149629721890835582834965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116199506295854447443779953 87149629721890835582834965)
                ·
                  refine ⟨4085138893213632917945389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87149629721890835582834965 4085138893213632917945389)
                  ·
                    refine ⟨1531927084955112344229521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4085138893213632917945389 1531927084955112344229521)
                    ·
                      refine ⟨1148945313716334258172141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1531927084955112344229521 1148945313716334258172141)
                      ·
                        rfl

theorem cell23_2237563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3, 2].length) (baseStart_2237563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237563 prefixEnd_2237563 := by exact prefixLift 2237563
  have htrace : WordTrace (prefixWord ++ tailWord_2237563) baseStart_2237563 baseEnd_2237563 := by
    simpa [prefixWord, tailWord_2237563, baseEnd_2237563] using wordTrace_append hprefix tailTrace_2237563
  have hstable : (prefixWord ++ tailWord_2237563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237563).length < 2 ^ (prefixWord ++ tailWord_2237563).sum := by decide
  have hdescent : baseEnd_2237563 < baseStart_2237563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237607 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2237607 : Nat := 118140960795 + 2237607 * 2 ^ 59
def prefixEnd_2237607 : Nat := 4983230072969 + 3 ^ 40 * 2237607 * 2
def baseEnd_2237607 : Nat := 382989302288377362007313

theorem tailTrace_2237607 : CollatzResearch.WordTrace tailWord_2237607 prefixEnd_2237607 382989302288377362007313 := by
  unfold tailWord_2237607
  simp only [CollatzResearch.WordTrace]
  refine ⟨81612232004539466695967075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54408154669692977797311383 81612232004539466695967075)
  ·
    refine ⟨122418348006809200043950613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81612232004539466695967075 122418348006809200043950613)
    ·
      refine ⟨5738360062819181252060185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122418348006809200043950613 5738360062819181252060185)
      ·
        refine ⟨4303770047114385939045139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5738360062819181252060185 4303770047114385939045139)
        ·
          refine ⟨6455655070671578908567709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4303770047114385939045139 6455655070671578908567709)
          ·
            refine ⟨2420870651501842090712891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6455655070671578908567709 2420870651501842090712891)
            ·
              refine ⟨3631305977252763136069337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420870651501842090712891 3631305977252763136069337)
              ·
                refine ⟨2723479482939572352052003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3631305977252763136069337 2723479482939572352052003)
                ·
                  refine ⟨4085219224409358528078005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723479482939572352052003 4085219224409358528078005)
                  ·
                    refine ⟨382989302288377362007313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4085219224409358528078005 382989302288377362007313)
                    ·
                      rfl

theorem cell23_2237607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2237607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237607 prefixEnd_2237607 := by exact prefixLift 2237607
  have htrace : WordTrace (prefixWord ++ tailWord_2237607) baseStart_2237607 baseEnd_2237607 := by
    simpa [prefixWord, tailWord_2237607, baseEnd_2237607] using wordTrace_append hprefix tailTrace_2237607
  have hstable : (prefixWord ++ tailWord_2237607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237607).length < 2 ^ (prefixWord ++ tailWord_2237607).sum := by decide
  have hdescent : baseEnd_2237607 < baseStart_2237607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237623 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_2237623 : Nat := 118140960795 + 2237623 * 2 ^ 59
def prefixEnd_2237623 : Nat := 4983230072969 + 3 ^ 40 * 2237623 * 2
def baseEnd_2237623 : Nat := 1148976122555604023421865

theorem tailTrace_2237623 : CollatzResearch.WordTrace tailWord_2237623 prefixEnd_2237623 1148976122555604023421865 := by
  unfold tailWord_2237623
  simp only [CollatzResearch.WordTrace]
  refine ⟨81612815572481501428549523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54408543714987667619033015 81612815572481501428549523)
  ·
    refine ⟨122419223358722252142824285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81612815572481501428549523 122419223358722252142824285)
    ·
      refine ⟨45907208759520844553559107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122419223358722252142824285 45907208759520844553559107)
      ·
        refine ⟨68860813139281266830338661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45907208759520844553559107 68860813139281266830338661)
        ·
          refine ⟨12911402463615237530688499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68860813139281266830338661 12911402463615237530688499)
          ·
            refine ⟨19367103695422856296032749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12911402463615237530688499 19367103695422856296032749)
            ·
              refine ⟨7262663885783571111012281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19367103695422856296032749 7262663885783571111012281)
              ·
                refine ⟨5446997914337678333259211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7262663885783571111012281 5446997914337678333259211)
                ·
                  refine ⟨8170496871506517499888817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446997914337678333259211 8170496871506517499888817)
                  ·
                    refine ⟨6127872653629888124916613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8170496871506517499888817 6127872653629888124916613)
                    ·
                      refine ⟨1148976122555604023421865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6127872653629888124916613 1148976122555604023421865)
                      ·
                        rfl

theorem cell23_2237623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_2237623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237623 prefixEnd_2237623 := by exact prefixLift 2237623
  have htrace : WordTrace (prefixWord ++ tailWord_2237623) baseStart_2237623 baseEnd_2237623 := by
    simpa [prefixWord, tailWord_2237623, baseEnd_2237623] using wordTrace_append hprefix tailTrace_2237623
  have hstable : (prefixWord ++ tailWord_2237623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237623).length < 2 ^ (prefixWord ++ tailWord_2237623).sum := by decide
  have hdescent : baseEnd_2237623 < baseStart_2237623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237630 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2237630 : Nat := 118140960795 + 2237630 * 2 ^ 59
def prefixEnd_2237630 : Nat := 4983230072969 + 3 ^ 40 * 2237630 * 2
def baseEnd_2237630 : Nat := 1148979716920185496034333

theorem tailTrace_2237630 : CollatzResearch.WordTrace tailWord_2237630 prefixEnd_2237630 1148979716920185496034333 := by
  unfold tailWord_2237630
  simp only [CollatzResearch.WordTrace]
  refine ⟨10201633860432017703006793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54408713922304094416036229 10201633860432017703006793)
  ·
    refine ⟨7651225395324013277255095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10201633860432017703006793 7651225395324013277255095)
    ·
      refine ⟨11476838092986019915882643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7651225395324013277255095 11476838092986019915882643)
      ·
        refine ⟨17215257139479029873823965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11476838092986019915882643 17215257139479029873823965)
        ·
          refine ⟨6455721427304636202683987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17215257139479029873823965 6455721427304636202683987)
          ·
            refine ⟨9683582140956954304025981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455721427304636202683987 9683582140956954304025981)
            ·
              refine ⟨3631343302858857864009743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9683582140956954304025981 3631343302858857864009743)
              ·
                refine ⟨5447014954288286796014615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3631343302858857864009743 5447014954288286796014615)
                ·
                  refine ⟨8170522431432430194021923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5447014954288286796014615 8170522431432430194021923)
                  ·
                    refine ⟨12255783647148645291032885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8170522431432430194021923 12255783647148645291032885)
                    ·
                      refine ⟨1148979716920185496034333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12255783647148645291032885 1148979716920185496034333)
                      ·
                        rfl

theorem cell23_2237630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2237630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237630 prefixEnd_2237630 := by exact prefixLift 2237630
  have htrace : WordTrace (prefixWord ++ tailWord_2237630) baseStart_2237630 baseEnd_2237630 := by
    simpa [prefixWord, tailWord_2237630, baseEnd_2237630] using wordTrace_append hprefix tailTrace_2237630
  have hstable : (prefixWord ++ tailWord_2237630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237630).length < 2 ^ (prefixWord ++ tailWord_2237630).sum := by decide
  have hdescent : baseEnd_2237630 < baseStart_2237630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237633 : List Nat := [1, 2, 6, 1, 1, 12]
def baseStart_2237633 : Nat := 118140960795 + 2237633 * 2 ^ 59
def prefixEnd_2237633 : Nat := 4983230072969 + 3 ^ 40 * 2237633 * 2
def baseEnd_2237633 : Nat := 4728317931531477301633

theorem tailTrace_2237633 : CollatzResearch.WordTrace tailWord_2237633 prefixEnd_2237633 4728317931531477301633 := by
  unfold tailWord_2237633
  simp only [CollatzResearch.WordTrace]
  refine ⟨81613180302445273136413553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54408786868296848757609035 81613180302445273136413553)
  ·
    refine ⟨61209885226833954852310165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81613180302445273136413553 61209885226833954852310165)
    ·
      refine ⟨2869213370007841633702039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61209885226833954852310165 2869213370007841633702039)
      ·
        refine ⟨4303820055011762450553059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869213370007841633702039 4303820055011762450553059)
        ·
          refine ⟨6455730082517643675829589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4303820055011762450553059 6455730082517643675829589)
          ·
            refine ⟨4728317931531477301633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6455730082517643675829589 4728317931531477301633)
            ·
              rfl

theorem cell23_2237633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 12].length) (baseStart_2237633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237633 prefixEnd_2237633 := by exact prefixLift 2237633
  have htrace : WordTrace (prefixWord ++ tailWord_2237633) baseStart_2237633 baseEnd_2237633 := by
    simpa [prefixWord, tailWord_2237633, baseEnd_2237633] using wordTrace_append hprefix tailTrace_2237633
  have hstable : (prefixWord ++ tailWord_2237633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237633).length < 2 ^ (prefixWord ++ tailWord_2237633).sum := by decide
  have hdescent : baseEnd_2237633 < baseStart_2237633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237694 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_2237694 : Nat := 118140960795 + 2237694 * 2 ^ 59
def prefixEnd_2237694 : Nat := 4983230072969 + 3 ^ 40 * 2237694 * 2
def baseEnd_2237694 : Nat := 1149012579682073245634039

theorem tailTrace_2237694 : CollatzResearch.WordTrace tailWord_2237694 prefixEnd_2237694 1149012579682073245634039 := by
  unfold tailWord_2237694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10201925644403035069298017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54410270103482853702922757 10201925644403035069298017)
  ·
    refine ⟨7651444233302276301973513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10201925644403035069298017 7651444233302276301973513)
    ·
      refine ⟨5738583174976707226480135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7651444233302276301973513 5738583174976707226480135)
      ·
        refine ⟨8607874762465060839720203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5738583174976707226480135 8607874762465060839720203)
        ·
          refine ⟨12911812143697591259580305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8607874762465060839720203 12911812143697591259580305)
          ·
            refine ⟨9683859107773193444685229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12911812143697591259580305 9683859107773193444685229)
            ·
              refine ⟨3631447165414947541756961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9683859107773193444685229 3631447165414947541756961)
              ·
                refine ⟨2723585374061210656317721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3631447165414947541756961 2723585374061210656317721)
                ·
                  refine ⟨2042689030545907992238291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2723585374061210656317721 2042689030545907992238291)
                  ·
                    refine ⟨3064033545818861988357437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2042689030545907992238291 3064033545818861988357437)
                    ·
                      refine ⟨1149012579682073245634039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3064033545818861988357437 1149012579682073245634039)
                      ·
                        rfl

theorem cell23_2237694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_2237694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237694 prefixEnd_2237694 := by exact prefixLift 2237694
  have htrace : WordTrace (prefixWord ++ tailWord_2237694) baseStart_2237694 baseEnd_2237694 := by
    simpa [prefixWord, tailWord_2237694, baseEnd_2237694] using wordTrace_append hprefix tailTrace_2237694
  have hstable : (prefixWord ++ tailWord_2237694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237694).length < 2 ^ (prefixWord ++ tailWord_2237694).sum := by decide
  have hdescent : baseEnd_2237694 < baseStart_2237694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237713 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_2237713 : Nat := 118140960795 + 2237713 * 2 ^ 59
def prefixEnd_2237713 : Nat := 4983230072969 + 3 ^ 40 * 2237713 * 2
def baseEnd_2237713 : Nat := 1149022335814508671296451

theorem tailTrace_2237713 : CollatzResearch.WordTrace tailWord_2237713 prefixEnd_2237713 1149022335814508671296451 := by
  unfold tailWord_2237713
  simp only [CollatzResearch.WordTrace]
  refine ⟨81616098142155446799325793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54410732094770297866217195 81616098142155446799325793)
  ·
    refine ⟨61212073606616585099494345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81616098142155446799325793 61212073606616585099494345)
    ·
      refine ⟨45909055204962438824620759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61212073606616585099494345 45909055204962438824620759)
      ·
        refine ⟨68863582807443658236931139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45909055204962438824620759 68863582807443658236931139)
        ·
          refine ⟨103295374211165487355396709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68863582807443658236931139 103295374211165487355396709)
          ·
            refine ⟨19367882664593528879136883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103295374211165487355396709 19367882664593528879136883)
            ·
              refine ⟨29051823996890293318705325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19367882664593528879136883 29051823996890293318705325)
              ·
                refine ⟨10894433998833859994514497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29051823996890293318705325 10894433998833859994514497)
                ·
                  refine ⟨8170825499125394995885873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10894433998833859994514497 8170825499125394995885873)
                  ·
                    refine ⟨6128119124344046246914405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8170825499125394995885873 6128119124344046246914405)
                    ·
                      refine ⟨1149022335814508671296451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6128119124344046246914405 1149022335814508671296451)
                      ·
                        rfl

theorem cell23_2237713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_2237713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237713 prefixEnd_2237713 := by exact prefixLift 2237713
  have htrace : WordTrace (prefixWord ++ tailWord_2237713) baseStart_2237713 baseEnd_2237713 := by
    simpa [prefixWord, tailWord_2237713, baseEnd_2237713] using wordTrace_append hprefix tailTrace_2237713
  have hstable : (prefixWord ++ tailWord_2237713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237713).length < 2 ^ (prefixWord ++ tailWord_2237713).sum := by decide
  have hdescent : baseEnd_2237713 < baseStart_2237713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237760 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 2, 5, 2]
def baseStart_2237760 : Nat := 118140960795 + 2237760 * 2 ^ 59
def prefixEnd_2237760 : Nat := 4983230072969 + 3 ^ 40 * 2237760 * 2
def baseEnd_2237760 : Nat := 1149046469405269987408735

theorem tailTrace_2237760 : CollatzResearch.WordTrace tailWord_2237760 prefixEnd_2237760 1149046469405269987408735 := by
  unfold tailWord_2237760
  simp only [CollatzResearch.WordTrace]
  refine ⟨40808906186492586913143367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54411874915323449217524489 40808906186492586913143367)
  ·
    refine ⟨61213359279738880369715051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40808906186492586913143367 61213359279738880369715051)
    ·
      refine ⟨91820038919608320554572577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61213359279738880369715051 91820038919608320554572577)
      ·
        refine ⟨68865029189706240415929433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91820038919608320554572577 68865029189706240415929433)
        ·
          refine ⟨51648771892279680311947075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68865029189706240415929433 51648771892279680311947075)
          ·
            refine ⟨77473157838419520467920613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51648771892279680311947075 77473157838419520467920613)
            ·
              refine ⟨14526217094703660087735115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77473157838419520467920613 14526217094703660087735115)
              ·
                refine ⟨21789325642055490131602673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14526217094703660087735115 21789325642055490131602673)
                ·
                  refine ⟨16341994231541617598702005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21789325642055490131602673 16341994231541617598702005)
                  ·
                    refine ⟨1532061959207026649878313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16341994231541617598702005 1532061959207026649878313)
                    ·
                      refine ⟨1149046469405269987408735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532061959207026649878313 1149046469405269987408735)
                      ·
                        rfl

theorem cell23_2237760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_2237760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237760 prefixEnd_2237760 := by exact prefixLift 2237760
  have htrace : WordTrace (prefixWord ++ tailWord_2237760) baseStart_2237760 baseEnd_2237760 := by
    simpa [prefixWord, tailWord_2237760, baseEnd_2237760] using wordTrace_append hprefix tailTrace_2237760
  have hstable : (prefixWord ++ tailWord_2237760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237760).length < 2 ^ (prefixWord ++ tailWord_2237760).sum := by decide
  have hdescent : baseEnd_2237760 < baseStart_2237760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237844 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2237844 : Nat := 118140960795 + 2237844 * 2 ^ 59
def prefixEnd_2237844 : Nat := 4983230072969 + 3 ^ 40 * 2237844 * 2
def baseEnd_2237844 : Nat := 1149089601780247658758349

theorem tailTrace_2237844 : CollatzResearch.WordTrace tailWord_2237844 prefixEnd_2237844 1149089601780247658758349 := by
  unfold tailWord_2237844
  simp only [CollatzResearch.WordTrace]
  refine ⟨40810438052340428086172293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54413917403120570781563057 40810438052340428086172293)
  ·
    refine ⟨7651957134813830266157305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40810438052340428086172293 7651957134813830266157305)
    ·
      refine ⟨5738967851110372699617979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7651957134813830266157305 5738967851110372699617979)
      ·
        refine ⟨8608451776665559049426969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5738967851110372699617979 8608451776665559049426969)
        ·
          refine ⟨6456338832499169287070227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8608451776665559049426969 6456338832499169287070227)
          ·
            refine ⟨9684508248748753930605341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6456338832499169287070227 9684508248748753930605341)
            ·
              refine ⟨3631690593280782723977003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9684508248748753930605341 3631690593280782723977003)
              ·
                refine ⟨5447535889921174085965505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3631690593280782723977003 5447535889921174085965505)
                ·
                  refine ⟨4085651917440880564474129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5447535889921174085965505 4085651917440880564474129)
                  ·
                    refine ⟨3064238938080660423355597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4085651917440880564474129 3064238938080660423355597)
                    ·
                      refine ⟨1149089601780247658758349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3064238938080660423355597 1149089601780247658758349)
                      ·
                        rfl

theorem cell23_2237844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2237844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237844 prefixEnd_2237844 := by exact prefixLift 2237844
  have htrace : WordTrace (prefixWord ++ tailWord_2237844) baseStart_2237844 baseEnd_2237844 := by
    simpa [prefixWord, tailWord_2237844, baseEnd_2237844] using wordTrace_append hprefix tailTrace_2237844
  have hstable : (prefixWord ++ tailWord_2237844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237844).length < 2 ^ (prefixWord ++ tailWord_2237844).sum := by decide
  have hdescent : baseEnd_2237844 < baseStart_2237844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237880 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_2237880 : Nat := 118140960795 + 2237880 * 2 ^ 59
def prefixEnd_2237880 : Nat := 4983230072969 + 3 ^ 40 * 2237880 * 2
def baseEnd_2237880 : Nat := 1149108087083809517908183

theorem tailTrace_2237880 : CollatzResearch.WordTrace tailWord_2237880 prefixEnd_2237880 1149108087083809517908183 := by
  unfold tailWord_2237880
  simp only [CollatzResearch.WordTrace]
  refine ⟨40811094566275217160327547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54414792755033622880436729 40811094566275217160327547)
  ·
    refine ⟨61216641849412825740491321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40811094566275217160327547 61216641849412825740491321)
    ·
      refine ⟨45912481387059619305368491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61216641849412825740491321 45912481387059619305368491)
      ·
        refine ⟨68868722080589428958052737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45912481387059619305368491 68868722080589428958052737)
        ·
          refine ⟨51651541560442071718539553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68868722080589428958052737 51651541560442071718539553)
          ·
            refine ⟨38738656170331553788904665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51651541560442071718539553 38738656170331553788904665)
            ·
              refine ⟨29053992127748665341678499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38738656170331553788904665 29053992127748665341678499)
              ·
                refine ⟨43580988191622998012517749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29053992127748665341678499 43580988191622998012517749)
                ·
                  refine ⟨4085717642964656063673539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43580988191622998012517749 4085717642964656063673539)
                  ·
                    refine ⟨6128576464446984095510309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4085717642964656063673539 6128576464446984095510309)
                    ·
                      refine ⟨1149108087083809517908183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6128576464446984095510309 1149108087083809517908183)
                      ·
                        rfl

theorem cell23_2237880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_2237880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237880 prefixEnd_2237880 := by exact prefixLift 2237880
  have htrace : WordTrace (prefixWord ++ tailWord_2237880) baseStart_2237880 baseEnd_2237880 := by
    simpa [prefixWord, tailWord_2237880, baseEnd_2237880] using wordTrace_append hprefix tailTrace_2237880
  have hstable : (prefixWord ++ tailWord_2237880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237880).length < 2 ^ (prefixWord ++ tailWord_2237880).sum := by decide
  have hdescent : baseEnd_2237880 < baseStart_2237880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237917 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2237917 : Nat := 118140960795 + 2237917 * 2 ^ 59
def prefixEnd_2237917 : Nat := 4983230072969 + 3 ^ 40 * 2237917 * 2
def baseEnd_2237917 : Nat := 1149127085868025873145513

theorem tailTrace_2237917 : CollatzResearch.WordTrace tailWord_2237917 prefixEnd_2237917 1149127085868025873145513 := by
  unfold tailWord_2237917
  simp only [CollatzResearch.WordTrace]
  refine ⟨81623538633416389639752005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54415692422277593093168003 81623538633416389639752005)
  ·
    refine ⟨15304413493765573057453501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81623538633416389639752005 15304413493765573057453501)
    ·
      refine ⟨5739155060162089896545063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15304413493765573057453501 5739155060162089896545063)
      ·
        refine ⟨8608732590243134844817595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5739155060162089896545063 8608732590243134844817595)
        ·
          refine ⟨12913098885364702267226393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8608732590243134844817595 12913098885364702267226393)
          ·
            refine ⟨9684824164023526700419795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12913098885364702267226393 9684824164023526700419795)
            ·
              refine ⟨14527236246035290050629693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9684824164023526700419795 14527236246035290050629693)
              ·
                refine ⟨5447713592263233768986135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14527236246035290050629693 5447713592263233768986135)
                ·
                  refine ⟨8171570388394850653479203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5447713592263233768986135 8171570388394850653479203)
                  ·
                    refine ⟨12257355582592275980218805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8171570388394850653479203 12257355582592275980218805)
                    ·
                      refine ⟨1149127085868025873145513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12257355582592275980218805 1149127085868025873145513)
                      ·
                        rfl

theorem cell23_2237917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2237917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237917 prefixEnd_2237917 := by exact prefixLift 2237917
  have htrace : WordTrace (prefixWord ++ tailWord_2237917) baseStart_2237917 baseEnd_2237917 := by
    simpa [prefixWord, tailWord_2237917, baseEnd_2237917] using wordTrace_append hprefix tailTrace_2237917
  have hstable : (prefixWord ++ tailWord_2237917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237917).length < 2 ^ (prefixWord ++ tailWord_2237917).sum := by decide
  have hdescent : baseEnd_2237917 < baseStart_2237917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237941 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2237941 : Nat := 118140960795 + 2237941 * 2 ^ 59
def prefixEnd_2237941 : Nat := 4983230072969 + 3 ^ 40 * 2237941 * 2
def baseEnd_2237941 : Nat := 383046469801244593081801

theorem tailTrace_2237941 : CollatzResearch.WordTrace tailWord_2237941 prefixEnd_2237941 383046469801244593081801 := by
  unfold tailWord_2237941
  simp only [CollatzResearch.WordTrace]
  refine ⟨81624413985329441738625677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54416275990219627825750451 81624413985329441738625677)
  ·
    refine ⟨30609155244498540651984629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81624413985329441738625677 30609155244498540651984629)
    ·
      refine ⟨2869608304171738186123559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30609155244498540651984629 2869608304171738186123559)
      ·
        refine ⟨4304412456257607279185339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869608304171738186123559 4304412456257607279185339)
        ·
          refine ⟨6456618684386410918778009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304412456257607279185339 6456618684386410918778009)
          ·
            refine ⟨4842464013289808189083507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6456618684386410918778009 4842464013289808189083507)
            ·
              refine ⟨7263696019934712283625261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842464013289808189083507 7263696019934712283625261)
              ·
                refine ⟨2723886007475517106359473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7263696019934712283625261 2723886007475517106359473)
                ·
                  refine ⟨2042914505606637829769605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2723886007475517106359473 2042914505606637829769605)
                  ·
                    refine ⟨383046469801244593081801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042914505606637829769605 383046469801244593081801)
                    ·
                      rfl

theorem cell23_2237941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2237941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237941 prefixEnd_2237941 := by exact prefixLift 2237941
  have htrace : WordTrace (prefixWord ++ tailWord_2237941) baseStart_2237941 baseEnd_2237941 := by
    simpa [prefixWord, tailWord_2237941, baseEnd_2237941] using wordTrace_append hprefix tailTrace_2237941
  have hstable : (prefixWord ++ tailWord_2237941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237941).length < 2 ^ (prefixWord ++ tailWord_2237941).sum := by decide
  have hdescent : baseEnd_2237941 < baseStart_2237941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237958 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2237958 : Nat := 118140960795 + 2237958 * 2 ^ 59
def prefixEnd_2237958 : Nat := 4983230072969 + 3 ^ 40 * 2237958 * 2
def baseEnd_2237958 : Nat := 383049379524953404244275

theorem tailTrace_2237958 : CollatzResearch.WordTrace tailWord_2237958 prefixEnd_2237958 383049379524953404244275 := by
  unfold tailWord_2237958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550782313320870426312329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54416689350845235761329685 2550782313320870426312329)
  ·
    refine ⟨1913086734990652819734247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2550782313320870426312329 1913086734990652819734247)
    ·
      refine ⟨2869630102485979229601371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913086734990652819734247 2869630102485979229601371)
      ·
        refine ⟨4304445153728968844402057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869630102485979229601371 4304445153728968844402057)
        ·
          refine ⟨3228333865296726633301543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4304445153728968844402057 3228333865296726633301543)
          ·
            refine ⟨4842500797945089949952315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228333865296726633301543 4842500797945089949952315)
            ·
              refine ⟨7263751196917634924928473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842500797945089949952315 7263751196917634924928473)
              ·
                refine ⟨5447813397688226193696355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7263751196917634924928473 5447813397688226193696355)
                ·
                  refine ⟨8171720096532339290544533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5447813397688226193696355 8171720096532339290544533)
                  ·
                    refine ⟨383049379524953404244275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8171720096532339290544533 383049379524953404244275)
                    ·
                      rfl

theorem cell23_2237958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2237958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237958 prefixEnd_2237958 := by exact prefixLift 2237958
  have htrace : WordTrace (prefixWord ++ tailWord_2237958) baseStart_2237958 baseEnd_2237958 := by
    simpa [prefixWord, tailWord_2237958, baseEnd_2237958] using wordTrace_append hprefix tailTrace_2237958
  have hstable : (prefixWord ++ tailWord_2237958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237958).length < 2 ^ (prefixWord ++ tailWord_2237958).sum := by decide
  have hdescent : baseEnd_2237958 < baseStart_2237958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237960 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2237960 : Nat := 118140960795 + 2237960 * 2 ^ 59
def prefixEnd_2237960 : Nat := 4983230072969 + 3 ^ 40 * 2237960 * 2
def baseEnd_2237960 : Nat := 1149149165536169204907815

theorem tailTrace_2237960 : CollatzResearch.WordTrace tailWord_2237960 prefixEnd_2237960 1149149165536169204907815 := by
  unfold tailWord_2237960
  simp only [CollatzResearch.WordTrace]
  refine ⟨40812553486130303991783667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54416737981507071989044889 40812553486130303991783667)
  ·
    refine ⟨61218830229195455987675501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40812553486130303991783667 61218830229195455987675501)
    ·
      refine ⟨22957061335948295995378313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61218830229195455987675501 22957061335948295995378313)
      ·
        refine ⟨17217796001961221996533735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22957061335948295995378313 17217796001961221996533735)
        ·
          refine ⟨25826694002941832994800603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17217796001961221996533735 25826694002941832994800603)
          ·
            refine ⟨38740041004412749492200905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25826694002941832994800603 38740041004412749492200905)
            ·
              refine ⟨29055030753309562119150679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38740041004412749492200905 29055030753309562119150679)
              ·
                refine ⟨43582546129964343178726019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29055030753309562119150679 43582546129964343178726019)
                ·
                  refine ⟨65373819194946514768089029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43582546129964343178726019 65373819194946514768089029)
                  ·
                    refine ⟨12257591099052471519016693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65373819194946514768089029 12257591099052471519016693)
                    ·
                      refine ⟨1149149165536169204907815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12257591099052471519016693 1149149165536169204907815)
                      ·
                        rfl

theorem cell23_2237960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2237960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237960 prefixEnd_2237960 := by exact prefixLift 2237960
  have htrace : WordTrace (prefixWord ++ tailWord_2237960) baseStart_2237960 baseEnd_2237960 := by
    simpa [prefixWord, tailWord_2237960, baseEnd_2237960] using wordTrace_append hprefix tailTrace_2237960
  have hstable : (prefixWord ++ tailWord_2237960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237960).length < 2 ^ (prefixWord ++ tailWord_2237960).sum := by decide
  have hdescent : baseEnd_2237960 < baseStart_2237960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237964 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_2237964 : Nat := 118140960795 + 2237964 * 2 ^ 59
def prefixEnd_2237964 : Nat := 4983230072969 + 3 ^ 40 * 2237964 * 2
def baseEnd_2237964 : Nat := 1149151219458787189257797

theorem tailTrace_2237964 : CollatzResearch.WordTrace tailWord_2237964 prefixEnd_2237964 1149151219458787189257797 := by
  unfold tailWord_2237964
  simp only [CollatzResearch.WordTrace]
  refine ⟨40812626432123058333356473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54416835242830744444475297 40812626432123058333356473)
  ·
    refine ⟨30609469824092293750017355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40812626432123058333356473 30609469824092293750017355)
    ·
      refine ⟨45914204736138440625026033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30609469824092293750017355 45914204736138440625026033)
      ·
        refine ⟨34435653552103830468769525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45914204736138440625026033 34435653552103830468769525)
        ·
          refine ⟨3228342520509734106447143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34435653552103830468769525 3228342520509734106447143)
          ·
            refine ⟨4842513780764601159670715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228342520509734106447143 4842513780764601159670715)
            ·
              refine ⟨7263770671146901739506073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842513780764601159670715 7263770671146901739506073)
              ·
                refine ⟨5447828003360176304629555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7263770671146901739506073 5447828003360176304629555)
                ·
                  refine ⟨8171742005040264456944333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5447828003360176304629555 8171742005040264456944333)
                  ·
                    refine ⟨3064403251890099171354125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8171742005040264456944333 3064403251890099171354125)
                    ·
                      refine ⟨1149151219458787189257797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3064403251890099171354125 1149151219458787189257797)
                      ·
                        rfl

theorem cell23_2237964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_2237964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237964 prefixEnd_2237964 := by exact prefixLift 2237964
  have htrace : WordTrace (prefixWord ++ tailWord_2237964) baseStart_2237964 baseEnd_2237964 := by
    simpa [prefixWord, tailWord_2237964, baseEnd_2237964] using wordTrace_append hprefix tailTrace_2237964
  have hstable : (prefixWord ++ tailWord_2237964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237964).length < 2 ^ (prefixWord ++ tailWord_2237964).sum := by decide
  have hdescent : baseEnd_2237964 < baseStart_2237964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237965 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2237965 : Nat := 118140960795 + 2237965 * 2 ^ 59
def prefixEnd_2237965 : Nat := 4983230072969 + 3 ^ 40 * 2237965 * 2
def baseEnd_2237965 : Nat := 1149151732939441685345293

theorem tailTrace_2237965 : CollatzResearch.WordTrace tailWord_2237965 prefixEnd_2237965 1149151732939441685345293 := by
  unfold tailWord_2237965
  simp only [CollatzResearch.WordTrace]
  refine ⟨81625289337242493837499349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54416859558161662558332899 81625289337242493837499349)
  ·
    refine ⟨1913092718841620949316391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 81625289337242493837499349 1913092718841620949316391)
    ·
      refine ⟨2869639078262431423974587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913092718841620949316391 2869639078262431423974587)
      ·
        refine ⟨4304458617393647135961881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869639078262431423974587 4304458617393647135961881)
        ·
          refine ⟨3228343963045235351971411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4304458617393647135961881 3228343963045235351971411)
          ·
            refine ⟨4842515944567853027957117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228343963045235351971411 4842515944567853027957117)
            ·
              refine ⟨1815943479212944885483919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4842515944567853027957117 1815943479212944885483919)
              ·
                refine ⟨2723915218819417328225879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815943479212944885483919 2723915218819417328225879)
                ·
                  refine ⟨4085872828229125992338819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723915218819417328225879 4085872828229125992338819)
                  ·
                    refine ⟨6128809242343688988508229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4085872828229125992338819 6128809242343688988508229)
                    ·
                      refine ⟨1149151732939441685345293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6128809242343688988508229 1149151732939441685345293)
                      ·
                        rfl

theorem cell23_2237965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2237965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237965 prefixEnd_2237965 := by exact prefixLift 2237965
  have htrace : WordTrace (prefixWord ++ tailWord_2237965) baseStart_2237965 baseEnd_2237965 := by
    simpa [prefixWord, tailWord_2237965, baseEnd_2237965] using wordTrace_append hprefix tailTrace_2237965
  have hstable : (prefixWord ++ tailWord_2237965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237965).length < 2 ^ (prefixWord ++ tailWord_2237965).sum := by decide
  have hdescent : baseEnd_2237965 < baseStart_2237965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237981 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2237981 : Nat := 118140960795 + 2237981 * 2 ^ 59
def prefixEnd_2237981 : Nat := 4983230072969 + 3 ^ 40 * 2237981 * 2
def baseEnd_2237981 : Nat := 1149159948629913622745219

theorem tailTrace_2237981 : CollatzResearch.WordTrace tailWord_2237981 prefixEnd_2237981 1149159948629913622745219 := by
  unfold tailWord_2237981
  simp only [CollatzResearch.WordTrace]
  refine ⟨81625872905184528570081797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54417248603456352380054531 81625872905184528570081797)
  ·
    refine ⟨15304851169722099106890337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81625872905184528570081797 15304851169722099106890337)
    ·
      refine ⟨11478638377291574330167753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15304851169722099106890337 11478638377291574330167753)
      ·
        refine ⟨8608978782968680747625815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11478638377291574330167753 8608978782968680747625815)
        ·
          refine ⟨12913468174453021121438723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8608978782968680747625815 12913468174453021121438723)
          ·
            refine ⟨19370202261679531682158085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12913468174453021121438723 19370202261679531682158085)
            ·
              refine ⟨3631912924064912190404641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19370202261679531682158085 3631912924064912190404641)
              ·
                refine ⟨2723934693048684142803481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3631912924064912190404641 2723934693048684142803481)
                ·
                  refine ⟨2042951019786513107102611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2723934693048684142803481 2042951019786513107102611)
                  ·
                    refine ⟨3064426529679769660653917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2042951019786513107102611 3064426529679769660653917)
                    ·
                      refine ⟨1149159948629913622745219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3064426529679769660653917 1149159948629913622745219)
                      ·
                        rfl

theorem cell23_2237981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2237981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2237981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2237981 prefixEnd_2237981 := by exact prefixLift 2237981
  have htrace : WordTrace (prefixWord ++ tailWord_2237981) baseStart_2237981 baseEnd_2237981 := by
    simpa [prefixWord, tailWord_2237981, baseEnd_2237981] using wordTrace_append hprefix tailTrace_2237981
  have hstable : (prefixWord ++ tailWord_2237981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237981).length < 2 ^ (prefixWord ++ tailWord_2237981).sum := by decide
  have hdescent : baseEnd_2237981 < baseStart_2237981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238017 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2238017 : Nat := 118140960795 + 2238017 * 2 ^ 59
def prefixEnd_2238017 : Nat := 4983230072969 + 3 ^ 40 * 2238017 * 2
def baseEnd_2238017 : Nat := 1149178433933475481895053

theorem tailTrace_2238017 : CollatzResearch.WordTrace tailWord_2238017 prefixEnd_2238017 1149178433933475481895053 := by
  unfold tailWord_2238017
  simp only [CollatzResearch.WordTrace]
  refine ⟨81627185933054106718392305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54418123955369404478928203 81627185933054106718392305)
  ·
    refine ⟨61220389449790580038794229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81627185933054106718392305 61220389449790580038794229)
    ·
      refine ⟨5739411510917866878636959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61220389449790580038794229 5739411510917866878636959)
      ·
        refine ⟨8609117266376800317955439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5739411510917866878636959 8609117266376800317955439)
        ·
          refine ⟨12913675899565200476933159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8609117266376800317955439 12913675899565200476933159)
          ·
            refine ⟨19370513849347800715399739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12913675899565200476933159 19370513849347800715399739)
            ·
              refine ⟨29055770774021701073099609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19370513849347800715399739 29055770774021701073099609)
              ·
                refine ⟨21791828080516275804824707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29055770774021701073099609 21791828080516275804824707)
                ·
                  refine ⟨32687742120774413707237061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21791828080516275804824707 32687742120774413707237061)
                  ·
                    refine ⟨6128951647645202570106949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32687742120774413707237061 6128951647645202570106949)
                    ·
                      refine ⟨1149178433933475481895053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6128951647645202570106949 1149178433933475481895053)
                      ·
                        rfl

theorem cell23_2238017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2238017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238017 prefixEnd_2238017 := by exact prefixLift 2238017
  have htrace : WordTrace (prefixWord ++ tailWord_2238017) baseStart_2238017 baseEnd_2238017 := by
    simpa [prefixWord, tailWord_2238017, baseEnd_2238017] using wordTrace_append hprefix tailTrace_2238017
  have hstable : (prefixWord ++ tailWord_2238017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238017).length < 2 ^ (prefixWord ++ tailWord_2238017).sum := by decide
  have hdescent : baseEnd_2238017 < baseStart_2238017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238044 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 7]
def baseStart_2238044 : Nat := 118140960795 + 2238044 * 2 ^ 59
def prefixEnd_2238044 : Nat := 4983230072969 + 3 ^ 40 * 2238044 * 2
def baseEnd_2238044 : Nat := 127688033101238541806381

theorem tailTrace_2238044 : CollatzResearch.WordTrace tailWord_2238044 prefixEnd_2238044 127688033101238541806381 := by
  unfold tailWord_2238044
  simp only [CollatzResearch.WordTrace]
  refine ⟨40814085351978145164812593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54418780469304193553083457 40814085351978145164812593)
  ·
    refine ⟨30610564013983608873609445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40814085351978145164812593 30610564013983608873609445)
    ·
      refine ⟨5739480752621926663801771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30610564013983608873609445 5739480752621926663801771)
      ·
        refine ⟨8609221128932889995702657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5739480752621926663801771 8609221128932889995702657)
        ·
          refine ⟨6456915846699667496776993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8609221128932889995702657 6456915846699667496776993)
          ·
            refine ⟨4842686885024750622582745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6456915846699667496776993 4842686885024750622582745)
            ·
              refine ⟨3632015163768562966937059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4842686885024750622582745 3632015163768562966937059)
              ·
                refine ⟨5448022745652844450405589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632015163768562966937059 5448022745652844450405589)
                ·
                  refine ⟨127688033101238541806381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5448022745652844450405589 127688033101238541806381)
                  ·
                    rfl

theorem cell23_2238044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_2238044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238044 prefixEnd_2238044 := by exact prefixLift 2238044
  have htrace : WordTrace (prefixWord ++ tailWord_2238044) baseStart_2238044 baseEnd_2238044 := by
    simpa [prefixWord, tailWord_2238044, baseEnd_2238044] using wordTrace_append hprefix tailTrace_2238044
  have hstable : (prefixWord ++ tailWord_2238044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238044).length < 2 ^ (prefixWord ++ tailWord_2238044).sum := by decide
  have hdescent : baseEnd_2238044 < baseStart_2238044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238094 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2238094 : Nat := 118140960795 + 2238094 * 2 ^ 59
def prefixEnd_2238094 : Nat := 4983230072969 + 3 ^ 40 * 2238094 * 2
def baseEnd_2238094 : Nat := 1149217971943871680632199

theorem tailTrace_2238094 : CollatzResearch.WordTrace tailWord_2238094 prefixEnd_2238094 1149217971943871680632199 := by
  unfold tailWord_2238094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10203749294221893608618167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54419996235850099245963557 10203749294221893608618167)
  ·
    refine ⟨15305623941332840412927251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10203749294221893608618167 15305623941332840412927251)
    ·
      refine ⟨22958435911999260619390877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15305623941332840412927251 22958435911999260619390877)
      ·
        refine ⟨8609413466999722732271579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22958435911999260619390877 8609413466999722732271579)
        ·
          refine ⟨12914120200499584098407369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8609413466999722732271579 12914120200499584098407369)
          ·
            refine ⟨9685590150374688073805527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12914120200499584098407369 9685590150374688073805527)
            ·
              refine ⟨14528385225562032110708291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9685590150374688073805527 14528385225562032110708291)
              ·
                refine ⟨21792577838343048166062437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14528385225562032110708291 21792577838343048166062437)
                ·
                  refine ⟨4086108344689321531136707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21792577838343048166062437 4086108344689321531136707)
                  ·
                    refine ⟨6129162517033982296705061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4086108344689321531136707 6129162517033982296705061)
                    ·
                      refine ⟨1149217971943871680632199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6129162517033982296705061 1149217971943871680632199)
                      ·
                        rfl

theorem cell23_2238094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2238094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238094 prefixEnd_2238094 := by exact prefixLift 2238094
  have htrace : WordTrace (prefixWord ++ tailWord_2238094) baseStart_2238094 baseEnd_2238094 := by
    simpa [prefixWord, tailWord_2238094, baseEnd_2238094] using wordTrace_append hprefix tailTrace_2238094
  have hstable : (prefixWord ++ tailWord_2238094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238094).length < 2 ^ (prefixWord ++ tailWord_2238094).sum := by decide
  have hdescent : baseEnd_2238094 < baseStart_2238094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238097 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_2238097 : Nat := 118140960795 + 2238097 * 2 ^ 59
def prefixEnd_2238097 : Nat := 4983230072969 + 3 ^ 40 * 2238097 * 2
def baseEnd_2238097 : Nat := 1149219512385835168894685

theorem tailTrace_2238097 : CollatzResearch.WordTrace tailWord_2238097 prefixEnd_2238097 1149219512385835168894685 := by
  unfold tailWord_2238097
  simp only [CollatzResearch.WordTrace]
  refine ⟨81630103772764280381304545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54420069181842853587536363 81630103772764280381304545)
  ·
    refine ⟨61222577829573210285978409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81630103772764280381304545 61222577829573210285978409)
    ·
      refine ⟨45916933372179907714483807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61222577829573210285978409 45916933372179907714483807)
      ·
        refine ⟨68875400058269861571725711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45916933372179907714483807 68875400058269861571725711)
        ·
          refine ⟨103313100087404792357588567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68875400058269861571725711 103313100087404792357588567)
          ·
            refine ⟨154969650131107188536382851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103313100087404792357588567 154969650131107188536382851)
            ·
              refine ⟨232454475196660782804574277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154969650131107188536382851 232454475196660782804574277)
              ·
                refine ⟨43585214099373896775857677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232454475196660782804574277 43585214099373896775857677)
                ·
                  refine ⟨16344455287265211290946629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43585214099373896775857677 16344455287265211290946629)
                  ·
                    refine ⟨3064585366362227117052493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16344455287265211290946629 3064585366362227117052493)
                    ·
                      refine ⟨1149219512385835168894685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3064585366362227117052493 1149219512385835168894685)
                      ·
                        rfl

theorem cell23_2238097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_2238097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238097 prefixEnd_2238097 := by exact prefixLift 2238097
  have htrace : WordTrace (prefixWord ++ tailWord_2238097) baseStart_2238097 baseEnd_2238097 := by
    simpa [prefixWord, tailWord_2238097, baseEnd_2238097] using wordTrace_append hprefix tailTrace_2238097
  have hstable : (prefixWord ++ tailWord_2238097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238097).length < 2 ^ (prefixWord ++ tailWord_2238097).sum := by decide
  have hdescent : baseEnd_2238097 < baseStart_2238097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238194 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_2238194 : Nat := 118140960795 + 2238194 * 2 ^ 59
def prefixEnd_2238194 : Nat := 4983230072969 + 3 ^ 40 * 2238194 * 2
def baseEnd_2238194 : Nat := 383089773336440429793913

theorem tailTrace_2238194 : CollatzResearch.WordTrace tailWord_2238194 prefixEnd_2238194 383089773336440429793913 := by
  unfold tailWord_2238194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408410413353216486896409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54422427768941910631723757 20408410413353216486896409)
  ·
    refine ⟨15306307810014912365172307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20408410413353216486896409 15306307810014912365172307)
    ·
      refine ⟨22959461715022368547758461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15306307810014912365172307 22959461715022368547758461)
      ·
        refine ⟨8609798143133388205409423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22959461715022368547758461 8609798143133388205409423)
        ·
          refine ⟨12914697214700082308114135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8609798143133388205409423 12914697214700082308114135)
          ·
            refine ⟨19372045822050123462171203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12914697214700082308114135 19372045822050123462171203)
            ·
              refine ⟨29058068733075185193256805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19372045822050123462171203 29058068733075185193256805)
              ·
                refine ⟨5448387887451597223735651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29058068733075185193256805 5448387887451597223735651)
                ·
                  refine ⟨8172581831177395835603477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448387887451597223735651 8172581831177395835603477)
                  ·
                    refine ⟨383089773336440429793913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8172581831177395835603477 383089773336440429793913)
                    ·
                      rfl

theorem cell23_2238194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_2238194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238194 prefixEnd_2238194 := by exact prefixLift 2238194
  have htrace : WordTrace (prefixWord ++ tailWord_2238194) baseStart_2238194 baseEnd_2238194 := by
    simpa [prefixWord, tailWord_2238194, baseEnd_2238194] using wordTrace_append hprefix tailTrace_2238194
  have hstable : (prefixWord ++ tailWord_2238194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238194).length < 2 ^ (prefixWord ++ tailWord_2238194).sum := by decide
  have hdescent : baseEnd_2238194 < baseStart_2238194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238198 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_2238198 : Nat := 118140960795 + 2238198 * 2 ^ 59
def prefixEnd_2238198 : Nat := 4983230072969 + 3 ^ 40 * 2238198 * 2
def baseEnd_2238198 : Nat := 383090457977313091243907

theorem tailTrace_2238198 : CollatzResearch.WordTrace tailWord_2238198 prefixEnd_2238198 383090457977313091243907 := by
  unfold tailWord_2238198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5102111721587398414420703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54422525030265583087154165 5102111721587398414420703)
  ·
    refine ⟨7653167582381097621631055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5102111721587398414420703 7653167582381097621631055)
    ·
      refine ⟨11479751373571646432446583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7653167582381097621631055 11479751373571646432446583)
      ·
        refine ⟨17219627060357469648669875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11479751373571646432446583 17219627060357469648669875)
        ·
          refine ⟨25829440590536204473004813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17219627060357469648669875 25829440590536204473004813)
          ·
            refine ⟨9686040221451076677376805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25829440590536204473004813 9686040221451076677376805)
            ·
              refine ⟨1816132541522076877008151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9686040221451076677376805 1816132541522076877008151)
              ·
                refine ⟨2724198812283115315512227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816132541522076877008151 2724198812283115315512227)
                ·
                  refine ⟨4086298218424672973268341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724198812283115315512227 4086298218424672973268341)
                  ·
                    refine ⟨383090457977313091243907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4086298218424672973268341 383090457977313091243907)
                    ·
                      rfl

theorem cell23_2238198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_2238198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238198 prefixEnd_2238198 := by exact prefixLift 2238198
  have htrace : WordTrace (prefixWord ++ tailWord_2238198) baseStart_2238198 baseEnd_2238198 := by
    simpa [prefixWord, tailWord_2238198, baseEnd_2238198] using wordTrace_append hprefix tailTrace_2238198
  have hstable : (prefixWord ++ tailWord_2238198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238198).length < 2 ^ (prefixWord ++ tailWord_2238198).sum := by decide
  have hdescent : baseEnd_2238198 < baseStart_2238198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238204 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_2238204 : Nat := 118140960795 + 2238204 * 2 ^ 59
def prefixEnd_2238204 : Nat := 4983230072969 + 3 ^ 40 * 2238204 * 2
def baseEnd_2238204 : Nat := 1149274454815866250256693

theorem tailTrace_2238204 : CollatzResearch.WordTrace tailWord_2238204 prefixEnd_2238204 1149274454815866250256693 := by
  unfold tailWord_2238204
  simp only [CollatzResearch.WordTrace]
  refine ⟨40817003191688318827724833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54422670922251091770299777 40817003191688318827724833)
  ·
    refine ⟨30612752393766239120793625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40817003191688318827724833 30612752393766239120793625)
    ·
      refine ⟨22959564295324679340595219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30612752393766239120793625 22959564295324679340595219)
      ·
        refine ⟨34439346442987019010892829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22959564295324679340595219 34439346442987019010892829)
        ·
          refine ⟨12914754916120132129084811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34439346442987019010892829 12914754916120132129084811)
          ·
            refine ⟨19372132374180198193627217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12914754916120132129084811 19372132374180198193627217)
            ·
              refine ⟨14529099280635148645220413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19372132374180198193627217 14529099280635148645220413)
              ·
                refine ⟨5448412230238180741957655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14529099280635148645220413 5448412230238180741957655)
                ·
                  refine ⟨8172618345357271112936483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448412230238180741957655 8172618345357271112936483)
                  ·
                    refine ⟨12258927518035906669404725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8172618345357271112936483 12258927518035906669404725)
                    ·
                      refine ⟨1149274454815866250256693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12258927518035906669404725 1149274454815866250256693)
                      ·
                        rfl

theorem cell23_2238204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_2238204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238204 prefixEnd_2238204 := by exact prefixLift 2238204
  have htrace : WordTrace (prefixWord ++ tailWord_2238204) baseStart_2238204 baseEnd_2238204 := by
    simpa [prefixWord, tailWord_2238204, baseEnd_2238204] using wordTrace_append hprefix tailTrace_2238204
  have hstable : (prefixWord ++ tailWord_2238204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238204).length < 2 ^ (prefixWord ++ tailWord_2238204).sum := by decide
  have hdescent : baseEnd_2238204 < baseStart_2238204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238211 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 2, 4]
def baseStart_2238211 : Nat := 118140960795 + 2238211 * 2 ^ 59
def prefixEnd_2238211 : Nat := 4983230072969 + 3 ^ 40 * 2238211 * 2
def baseEnd_2238211 : Nat := 383092683060149240956387

theorem tailTrace_2238211 : CollatzResearch.WordTrace tailWord_2238211 prefixEnd_2238211 383092683060149240956387 := by
  unfold tailWord_2238211
  simp only [CollatzResearch.WordTrace]
  refine ⟨81634261694351277850954487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54422841129567518567302991 81634261694351277850954487)
  ·
    refine ⟨122451392541526916776431731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81634261694351277850954487 122451392541526916776431731)
    ·
      refine ⟨183677088812290375164647597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122451392541526916776431731 183677088812290375164647597)
      ·
        refine ⟨68878908304608890686742849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183677088812290375164647597 68878908304608890686742849)
        ·
          refine ⟨51659181228456668015057137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68878908304608890686742849 51659181228456668015057137)
          ·
            refine ⟨38744385921342501011292853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51659181228456668015057137 38744385921342501011292853)
            ·
              refine ⟨3632286180125859469808705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38744385921342501011292853 3632286180125859469808705)
              ·
                refine ⟨2724214635094394602356529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632286180125859469808705 2724214635094394602356529)
                ·
                  refine ⟨2043160976320795951767397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2724214635094394602356529 2043160976320795951767397)
                  ·
                    refine ⟨383092683060149240956387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2043160976320795951767397 383092683060149240956387)
                    ·
                      rfl

theorem cell23_2238211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 4].length) (baseStart_2238211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238211 prefixEnd_2238211 := by exact prefixLift 2238211
  have htrace : WordTrace (prefixWord ++ tailWord_2238211) baseStart_2238211 baseEnd_2238211 := by
    simpa [prefixWord, tailWord_2238211, baseEnd_2238211] using wordTrace_append hprefix tailTrace_2238211
  have hstable : (prefixWord ++ tailWord_2238211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238211).length < 2 ^ (prefixWord ++ tailWord_2238211).sum := by decide
  have hdescent : baseEnd_2238211 < baseStart_2238211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238217 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_2238217 : Nat := 118140960795 + 2238217 * 2 ^ 59
def prefixEnd_2238217 : Nat := 4983230072969 + 3 ^ 40 * 2238217 * 2
def baseEnd_2238217 : Nat := 1149281130064374699394133

theorem tailTrace_2238217 : CollatzResearch.WordTrace tailWord_2238217 prefixEnd_2238217 1149281130064374699394133 := by
  unfold tailWord_2238217
  simp only [CollatzResearch.WordTrace]
  refine ⟨81634480532329540875672905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54422987021553027250448603 81634480532329540875672905)
  ·
    refine ⟨61225860399247155656754679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81634480532329540875672905 61225860399247155656754679)
    ·
      refine ⟨91838790598870733485132019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61225860399247155656754679 91838790598870733485132019)
      ·
        refine ⟨137758185898306100227698029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91838790598870733485132019 137758185898306100227698029)
        ·
          refine ⟨51659319711864787585386761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137758185898306100227698029 51659319711864787585386761)
          ·
            refine ⟨38744489783898590689040071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51659319711864787585386761 38744489783898590689040071)
            ·
              refine ⟨58116734675847886033560107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38744489783898590689040071 58116734675847886033560107)
              ·
                refine ⟨87175102013771829050340161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58116734675847886033560107 87175102013771829050340161)
                ·
                  refine ⟨65381326510328871787755121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87175102013771829050340161 65381326510328871787755121)
                  ·
                    refine ⟨49035994882746653840816341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65381326510328871787755121 49035994882746653840816341)
                    ·
                      refine ⟨1149281130064374699394133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49035994882746653840816341 1149281130064374699394133)
                      ·
                        rfl

theorem cell23_2238217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_2238217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238217 prefixEnd_2238217 := by exact prefixLift 2238217
  have htrace : WordTrace (prefixWord ++ tailWord_2238217) baseStart_2238217 baseEnd_2238217 := by
    simpa [prefixWord, tailWord_2238217, baseEnd_2238217] using wordTrace_append hprefix tailTrace_2238217
  have hstable : (prefixWord ++ tailWord_2238217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238217).length < 2 ^ (prefixWord ++ tailWord_2238217).sum := by decide
  have hdescent : baseEnd_2238217 < baseStart_2238217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238218 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_2238218 : Nat := 118140960795 + 2238218 * 2 ^ 59
def prefixEnd_2238218 : Nat := 4983230072969 + 3 ^ 40 * 2238218 * 2
def baseEnd_2238218 : Nat := 1149281643545029195481629

theorem tailTrace_2238218 : CollatzResearch.WordTrace tailWord_2238218 prefixEnd_2238218 1149281643545029195481629 := by
  unfold tailWord_2238218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408629251331479511614827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54423011336883945364306205 20408629251331479511614827)
  ·
    refine ⟨30612943876997219267422241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20408629251331479511614827 30612943876997219267422241)
    ·
      refine ⟨22959707907747914450566681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30612943876997219267422241 22959707907747914450566681)
      ·
        refine ⟨17219780930810935837925011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22959707907747914450566681 17219780930810935837925011)
        ·
          refine ⟨25829671396216403756887517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17219780930810935837925011 25829671396216403756887517)
          ·
            refine ⟨9686126773581151408832819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25829671396216403756887517 9686126773581151408832819)
            ·
              refine ⟨14529190160371727113249229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9686126773581151408832819 14529190160371727113249229)
              ·
                refine ⟨5448446310139397667468461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14529190160371727113249229 5448446310139397667468461)
                ·
                  refine ⟨2043167366302274125300673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5448446310139397667468461 2043167366302274125300673)
                  ·
                    refine ⟨1532375524726705593975505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2043167366302274125300673 1532375524726705593975505)
                    ·
                      refine ⟨1149281643545029195481629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532375524726705593975505 1149281643545029195481629)
                      ·
                        rfl

theorem cell23_2238218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_2238218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238218 prefixEnd_2238218 := by exact prefixLift 2238218
  have htrace : WordTrace (prefixWord ++ tailWord_2238218) baseStart_2238218 baseEnd_2238218 := by
    simpa [prefixWord, tailWord_2238218, baseEnd_2238218] using wordTrace_append hprefix tailTrace_2238218
  have hstable : (prefixWord ++ tailWord_2238218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238218).length < 2 ^ (prefixWord ++ tailWord_2238218).sum := by decide
  have hdescent : baseEnd_2238218 < baseStart_2238218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238227 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6]
def baseStart_2238227 : Nat := 118140960795 + 2238227 * 2 ^ 59
def prefixEnd_2238227 : Nat := 4983230072969 + 3 ^ 40 * 2238227 * 2
def baseEnd_2238227 : Nat := 1149286264870919660269087

theorem tailTrace_2238227 : CollatzResearch.WordTrace tailWord_2238227 prefixEnd_2238227 1149286264870919660269087 := by
  unfold tailWord_2238227
  simp only [CollatzResearch.WordTrace]
  refine ⟨81634845262293312583536935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54423230174862208389024623 81634845262293312583536935)
  ·
    refine ⟨122452267893439968875305403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81634845262293312583536935 122452267893439968875305403)
    ·
      refine ⟨183678401840159953312958105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122452267893439968875305403 183678401840159953312958105)
      ·
        refine ⟨137758801380119964984718579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183678401840159953312958105 137758801380119964984718579)
        ·
          refine ⟨206638202070179947477077869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137758801380119964984718579 206638202070179947477077869)
          ·
            refine ⟨77489325776317480303904201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206638202070179947477077869 77489325776317480303904201)
            ·
              refine ⟨58116994332238110227928151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77489325776317480303904201 58116994332238110227928151)
              ·
                refine ⟨87175491498357165341892227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58116994332238110227928151 87175491498357165341892227)
                ·
                  refine ⟨130763237247535748012838341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87175491498357165341892227 130763237247535748012838341)
                  ·
                    refine ⟨24518106983912952752407189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130763237247535748012838341 24518106983912952752407189)
                    ·
                      refine ⟨1149286264870919660269087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24518106983912952752407189 1149286264870919660269087)
                      ·
                        rfl

theorem cell23_2238227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_2238227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238227 prefixEnd_2238227 := by exact prefixLift 2238227
  have htrace : WordTrace (prefixWord ++ tailWord_2238227) baseStart_2238227 baseEnd_2238227 := by
    simpa [prefixWord, tailWord_2238227, baseEnd_2238227] using wordTrace_append hprefix tailTrace_2238227
  have hstable : (prefixWord ++ tailWord_2238227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238227).length < 2 ^ (prefixWord ++ tailWord_2238227).sum := by decide
  have hdescent : baseEnd_2238227 < baseStart_2238227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238231 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2238231 : Nat := 118140960795 + 2238231 * 2 ^ 59
def prefixEnd_2238231 : Nat := 4983230072969 + 3 ^ 40 * 2238231 * 2
def baseEnd_2238231 : Nat := 1149288318793537644619069

theorem tailTrace_2238231 : CollatzResearch.WordTrace tailWord_2238231 prefixEnd_2238231 1149288318793537644619069 := by
  unfold tailWord_2238231
  simp only [CollatzResearch.WordTrace]
  refine ⟨81634991154278821266682547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54423327436185880844455031 81634991154278821266682547)
  ·
    refine ⟨122452486731418231900023821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81634991154278821266682547 122452486731418231900023821)
    ·
      refine ⟨45919682524281836962508933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122452486731418231900023821 45919682524281836962508933)
      ·
        refine ⟨8609940473302844430470425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45919682524281836962508933 8609940473302844430470425)
        ·
          refine ⟨6457455354977133322852819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8609940473302844430470425 6457455354977133322852819)
          ·
            refine ⟨9686183032465699984279229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457455354977133322852819 9686183032465699984279229)
            ·
              refine ⟨3632318637174637494104711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9686183032465699984279229 3632318637174637494104711)
              ·
                refine ⟨5448477955761956241157067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632318637174637494104711 5448477955761956241157067)
                ·
                  refine ⟨8172716933642934361735601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448477955761956241157067 8172716933642934361735601)
                  ·
                    refine ⟨6129537700232200771301701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8172716933642934361735601 6129537700232200771301701)
                    ·
                      refine ⟨1149288318793537644619069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6129537700232200771301701 1149288318793537644619069)
                      ·
                        rfl

theorem cell23_2238231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2238231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238231 prefixEnd_2238231 := by exact prefixLift 2238231
  have htrace : WordTrace (prefixWord ++ tailWord_2238231) baseStart_2238231 baseEnd_2238231 := by
    simpa [prefixWord, tailWord_2238231, baseEnd_2238231] using wordTrace_append hprefix tailTrace_2238231
  have hstable : (prefixWord ++ tailWord_2238231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238231).length < 2 ^ (prefixWord ++ tailWord_2238231).sum := by decide
  have hdescent : baseEnd_2238231 < baseStart_2238231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238241 : List Nat := [1, 2, 3, 2, 1, 5, 2, 7]
def baseStart_2238241 : Nat := 118140960795 + 2238241 * 2 ^ 59
def prefixEnd_2238241 : Nat := 4983230072969 + 3 ^ 40 * 2238241 * 2
def baseEnd_2238241 : Nat := 42566424207410466870149

theorem tailTrace_2238241 : CollatzResearch.WordTrace tailWord_2238241 prefixEnd_2238241 42566424207410466870149 := by
  unfold tailWord_2238241
  simp only [CollatzResearch.WordTrace]
  refine ⟨81635355884242592974546577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54423570589495061983031051 81635355884242592974546577)
  ·
    refine ⟨61226516913181944730909933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81635355884242592974546577 61226516913181944730909933)
    ·
      refine ⟨22959943842443229274091225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61226516913181944730909933 22959943842443229274091225)
      ·
        refine ⟨17219957881832421955568419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22959943842443229274091225 17219957881832421955568419)
        ·
          refine ⟨25829936822748632933352629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17219957881832421955568419 25829936822748632933352629)
          ·
            refine ⟨2421556577132684337501809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25829936822748632933352629 2421556577132684337501809)
            ·
              refine ⟨1816167432849513253126357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421556577132684337501809 1816167432849513253126357)
              ·
                refine ⟨42566424207410466870149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1816167432849513253126357 42566424207410466870149)
                ·
                  rfl

theorem cell23_2238241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 7].length) (baseStart_2238241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238241 prefixEnd_2238241 := by exact prefixLift 2238241
  have htrace : WordTrace (prefixWord ++ tailWord_2238241) baseStart_2238241 baseEnd_2238241 := by
    simpa [prefixWord, tailWord_2238241, baseEnd_2238241] using wordTrace_append hprefix tailTrace_2238241
  have hstable : (prefixWord ++ tailWord_2238241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238241).length < 2 ^ (prefixWord ++ tailWord_2238241).sum := by decide
  have hdescent : baseEnd_2238241 < baseStart_2238241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238252 : List Nat := [2, 2, 1, 1, 1, 7, 1, 3, 1, 2, 2]
def baseStart_2238252 : Nat := 118140960795 + 2238252 * 2 ^ 59
def prefixEnd_2238252 : Nat := 4983230072969 + 3 ^ 40 * 2238252 * 2
def baseEnd_2238252 : Nat := 1149299101887282062456473

theorem tailTrace_2238252 : CollatzResearch.WordTrace tailWord_2238252 prefixEnd_2238252 1149299101887282062456473 := by
  unfold tailWord_2238252
  simp only [CollatzResearch.WordTrace]
  refine ⟨40817878543601370926598505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54423838058135161235464673 40817878543601370926598505)
  ·
    refine ⟨30613408907701028194948879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40817878543601370926598505 30613408907701028194948879)
    ·
      refine ⟨45920113361551542292423319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30613408907701028194948879 45920113361551542292423319)
      ·
        refine ⟨68880170042327313438634979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45920113361551542292423319 68880170042327313438634979)
        ·
          refine ⟨103320255063490970157952469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68880170042327313438634979 103320255063490970157952469)
          ·
            refine ⟨2421568478050569613077011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103320255063490970157952469 2421568478050569613077011)
            ·
              refine ⟨3632352717075854419615517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421568478050569613077011 3632352717075854419615517)
              ·
                refine ⟨1362132268903445407355819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3632352717075854419615517 1362132268903445407355819)
                ·
                  refine ⟨2043198403355168111033729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362132268903445407355819 2043198403355168111033729)
                  ·
                    refine ⟨1532398802516376083275297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2043198403355168111033729 1532398802516376083275297)
                    ·
                      refine ⟨1149299101887282062456473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532398802516376083275297 1149299101887282062456473)
                      ·
                        rfl

theorem cell23_2238252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_2238252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238252 prefixEnd_2238252 := by exact prefixLift 2238252
  have htrace : WordTrace (prefixWord ++ tailWord_2238252) baseStart_2238252 baseEnd_2238252 := by
    simpa [prefixWord, tailWord_2238252, baseEnd_2238252] using wordTrace_append hprefix tailTrace_2238252
  have hstable : (prefixWord ++ tailWord_2238252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238252).length < 2 ^ (prefixWord ++ tailWord_2238252).sum := by decide
  have hdescent : baseEnd_2238252 < baseStart_2238252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238269 : List Nat := [1, 4, 1, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_2238269 : Nat := 118140960795 + 2238269 * 2 ^ 59
def prefixEnd_2238269 : Nat := 4983230072969 + 3 ^ 40 * 2238269 * 2
def baseEnd_2238269 : Nat := 1149307831058408495943895

theorem tailTrace_2238269 : CollatzResearch.WordTrace tailWord_2238269 prefixEnd_2238269 1149307831058408495943895 := by
  unfold tailWord_2238269
  simp only [CollatzResearch.WordTrace]
  refine ⟨81636377128141153756565861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54424251418760769171043907 81636377128141153756565861)
  ·
    refine ⟨15306820711526466329356099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81636377128141153756565861 15306820711526466329356099)
    ·
      refine ⟨22960231067289699494034149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15306820711526466329356099 22960231067289699494034149)
      ·
        refine ⟨4305043325116818655131403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22960231067289699494034149 4305043325116818655131403)
        ·
          refine ⟨6457564987675227982697105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4305043325116818655131403 6457564987675227982697105)
          ·
            refine ⟨4843173740756420987022829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6457564987675227982697105 4843173740756420987022829)
            ·
              refine ⟨1816190152783657870133561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4843173740756420987022829 1816190152783657870133561)
              ·
                refine ⟨1362142614587743402600171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816190152783657870133561 1362142614587743402600171)
                ·
                  refine ⟨2043213921881615103900257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362142614587743402600171 2043213921881615103900257)
                  ·
                    refine ⟨1532410441411211327925193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2043213921881615103900257 1532410441411211327925193)
                    ·
                      refine ⟨1149307831058408495943895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532410441411211327925193 1149307831058408495943895)
                      ·
                        rfl

theorem cell23_2238269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_2238269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238269 prefixEnd_2238269 := by exact prefixLift 2238269
  have htrace : WordTrace (prefixWord ++ tailWord_2238269) baseStart_2238269 baseEnd_2238269 := by
    simpa [prefixWord, tailWord_2238269, baseEnd_2238269] using wordTrace_append hprefix tailTrace_2238269
  have hstable : (prefixWord ++ tailWord_2238269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238269).length < 2 ^ (prefixWord ++ tailWord_2238269).sum := by decide
  have hdescent : baseEnd_2238269 < baseStart_2238269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238341 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_2238341 : Nat := 118140960795 + 2238341 * 2 ^ 59
def prefixEnd_2238341 : Nat := 4983230072969 + 3 ^ 40 * 2238341 * 2
def baseEnd_2238341 : Nat := 1149344801665532214243563

theorem tailTrace_2238341 : CollatzResearch.WordTrace tailWord_2238341 prefixEnd_2238341 1149344801665532214243563 := by
  unfold tailWord_2238341
  simp only [CollatzResearch.WordTrace]
  refine ⟨81639003183880310053186877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54426002122586873368791251 81639003183880310053186877)
  ·
    refine ⟨30614626193955116269945079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81639003183880310053186877 30614626193955116269945079)
    ·
      refine ⟨45921939290932674404917619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30614626193955116269945079 45921939290932674404917619)
      ·
        refine ⟨68882908936399011607376429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45921939290932674404917619 68882908936399011607376429)
        ·
          refine ⟨25831090851149629352766161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68882908936399011607376429 25831090851149629352766161)
          ·
            refine ⟨19373318138362222014574621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25831090851149629352766161 19373318138362222014574621)
            ·
              refine ⟨7264994301885833255465483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19373318138362222014574621 7264994301885833255465483)
              ·
                refine ⟨10897491452828749883198225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7264994301885833255465483 10897491452828749883198225)
                ·
                  refine ⟨8173118589621562412398669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10897491452828749883198225 8173118589621562412398669)
                  ·
                    refine ⟨3064919471108085904649501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8173118589621562412398669 3064919471108085904649501)
                    ·
                      refine ⟨1149344801665532214243563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3064919471108085904649501 1149344801665532214243563)
                      ·
                        rfl

theorem cell23_2238341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_2238341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238341 prefixEnd_2238341 := by exact prefixLift 2238341
  have htrace : WordTrace (prefixWord ++ tailWord_2238341) baseStart_2238341 baseEnd_2238341 := by
    simpa [prefixWord, tailWord_2238341, baseEnd_2238341] using wordTrace_append hprefix tailTrace_2238341
  have hstable : (prefixWord ++ tailWord_2238341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238341).length < 2 ^ (prefixWord ++ tailWord_2238341).sum := by decide
  have hdescent : baseEnd_2238341 < baseStart_2238341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238361 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 2, 5]
def baseStart_2238361 : Nat := 118140960795 + 2238361 * 2 ^ 59
def prefixEnd_2238361 : Nat := 4983230072969 + 3 ^ 40 * 2238361 * 2
def baseEnd_2238361 : Nat := 383118357092874045331157

theorem tailTrace_2238361 : CollatzResearch.WordTrace tailWord_2238361 prefixEnd_2238361 383118357092874045331157 := by
  unfold tailWord_2238361
  simp only [CollatzResearch.WordTrace]
  refine ⟨81639732643807853468914937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54426488429205235645943291 81639732643807853468914937)
  ·
    refine ⟨61229799482855890101686203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81639732643807853468914937 61229799482855890101686203)
    ·
      refine ⟨91844699224283835152529305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61229799482855890101686203 91844699224283835152529305)
      ·
        refine ⟨68883524418212876364396979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91844699224283835152529305 68883524418212876364396979)
        ·
          refine ⟨103325286627319314546595469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68883524418212876364396979 103325286627319314546595469)
          ·
            refine ⟨38746982485244742954973301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103325286627319314546595469 38746982485244742954973301)
            ·
              refine ⟨3632529607991694652028747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38746982485244742954973301 3632529607991694652028747)
              ·
                refine ⟨5448794411987541978043121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632529607991694652028747 5448794411987541978043121)
                ·
                  refine ⟨4086595808990656483532341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5448794411987541978043121 4086595808990656483532341)
                  ·
                    refine ⟨383118357092874045331157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4086595808990656483532341 383118357092874045331157)
                    ·
                      rfl

theorem cell23_2238361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_2238361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238361 prefixEnd_2238361 := by exact prefixLift 2238361
  have htrace : WordTrace (prefixWord ++ tailWord_2238361) baseStart_2238361 baseEnd_2238361 := by
    simpa [prefixWord, tailWord_2238361, baseEnd_2238361] using wordTrace_append hprefix tailTrace_2238361
  have hstable : (prefixWord ++ tailWord_2238361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238361).length < 2 ^ (prefixWord ++ tailWord_2238361).sum := by decide
  have hdescent : baseEnd_2238361 < baseStart_2238361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238376 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2238376 : Nat := 118140960795 + 2238376 * 2 ^ 59
def prefixEnd_2238376 : Nat := 4983230072969 + 3 ^ 40 * 2238376 * 2
def baseEnd_2238376 : Nat := 1149362773488439577305903

theorem tailTrace_2238376 : CollatzResearch.WordTrace tailWord_2238376 prefixEnd_2238376 1149362773488439577305903 := by
  unfold tailWord_2238376
  simp only [CollatzResearch.WordTrace]
  refine ⟨40820139869376755515355491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54426853159169007353807321 40820139869376755515355491)
  ·
    refine ⟨61230209804065133273033237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40820139869376755515355491 61230209804065133273033237)
    ·
      refine ⟨2870166084565553122173433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61230209804065133273033237 2870166084565553122173433)
      ·
        refine ⟨2152624563424164841630075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2870166084565553122173433 2152624563424164841630075)
        ·
          refine ⟨3228936845136247262445113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152624563424164841630075 3228936845136247262445113)
          ·
            refine ⟨2421702633852185446833835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228936845136247262445113 2421702633852185446833835)
            ·
              refine ⟨3632553950778278170250753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421702633852185446833835 3632553950778278170250753)
              ·
                refine ⟨2724415463083708627688065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632553950778278170250753 2724415463083708627688065)
                ·
                  refine ⟨2043311597312781470766049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2724415463083708627688065 2043311597312781470766049)
                  ·
                    refine ⟨1532483697984586103074537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2043311597312781470766049 1532483697984586103074537)
                    ·
                      refine ⟨1149362773488439577305903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532483697984586103074537 1149362773488439577305903)
                      ·
                        rfl

theorem cell23_2238376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2238376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238376 prefixEnd_2238376 := by exact prefixLift 2238376
  have htrace : WordTrace (prefixWord ++ tailWord_2238376) baseStart_2238376 baseEnd_2238376 := by
    simpa [prefixWord, tailWord_2238376, baseEnd_2238376] using wordTrace_append hprefix tailTrace_2238376
  have hstable : (prefixWord ++ tailWord_2238376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238376).length < 2 ^ (prefixWord ++ tailWord_2238376).sum := by decide
  have hdescent : baseEnd_2238376 < baseStart_2238376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238382 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_2238382 : Nat := 118140960795 + 2238382 * 2 ^ 59
def prefixEnd_2238382 : Nat := 4983230072969 + 3 ^ 40 * 2238382 * 2
def baseEnd_2238382 : Nat := 127707317152485172647875

theorem tailTrace_2238382 : CollatzResearch.WordTrace tailWord_2238382 prefixEnd_2238382 127707317152485172647875 := by
  unfold tailWord_2238382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10205062322091471756928675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54426999051154516036952933 10205062322091471756928675)
  ·
    refine ⟨15307593483137207635393013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10205062322091471756928675 15307593483137207635393013)
    ·
      refine ⟨1435086889044113215818095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15307593483137207635393013 1435086889044113215818095)
      ·
        refine ⟨2152630333566169823727143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1435086889044113215818095 2152630333566169823727143)
        ·
          refine ⟨3228945500349254735590715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152630333566169823727143 3228945500349254735590715)
          ·
            refine ⟨4843418250523882103386073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228945500349254735590715 4843418250523882103386073)
            ·
              refine ⟨3632563687892911577539555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4843418250523882103386073 3632563687892911577539555)
              ·
                refine ⟨5448845531839367366309333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632563687892911577539555 5448845531839367366309333)
                ·
                  refine ⟨127707317152485172647875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5448845531839367366309333 127707317152485172647875)
                  ·
                    rfl

theorem cell23_2238382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_2238382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238382 prefixEnd_2238382 := by exact prefixLift 2238382
  have htrace : WordTrace (prefixWord ++ tailWord_2238382) baseStart_2238382 baseEnd_2238382 := by
    simpa [prefixWord, tailWord_2238382, baseEnd_2238382] using wordTrace_append hprefix tailTrace_2238382
  have hstable : (prefixWord ++ tailWord_2238382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238382).length < 2 ^ (prefixWord ++ tailWord_2238382).sum := by decide
  have hdescent : baseEnd_2238382 < baseStart_2238382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238408 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 3, 4]
def baseStart_2238408 : Nat := 118140960795 + 2238408 * 2 ^ 59
def prefixEnd_2238408 : Nat := 4983230072969 + 3 ^ 40 * 2238408 * 2
def baseEnd_2238408 : Nat := 383126401623127817368585

theorem tailTrace_2238408 : CollatzResearch.WordTrace tailWord_2238408 prefixEnd_2238408 383126401623127817368585 := by
  unfold tailWord_2238408
  simp only [CollatzResearch.WordTrace]
  refine ⟨40820723437318790247937939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54427631249758386997250585 40820723437318790247937939)
  ·
    refine ⟨61231085155978185371906909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40820723437318790247937939 61231085155978185371906909)
    ·
      refine ⟨22961656933491819514465091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61231085155978185371906909 22961656933491819514465091)
      ·
        refine ⟨34442485400237729271697637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22961656933491819514465091 34442485400237729271697637)
        ·
          refine ⟨6457966012544574238443307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34442485400237729271697637 6457966012544574238443307)
          ·
            refine ⟨9686949018816861357664961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457966012544574238443307 9686949018816861357664961)
            ·
              refine ⟨7265211764112646018248721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9686949018816861357664961 7265211764112646018248721)
              ·
                refine ⟨5448908823084484513686541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7265211764112646018248721 5448908823084484513686541)
                ·
                  refine ⟨2043340808656681692632453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5448908823084484513686541 2043340808656681692632453)
                  ·
                    refine ⟨383126401623127817368585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2043340808656681692632453 383126401623127817368585)
                    ·
                      rfl

theorem cell23_2238408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_2238408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238408 prefixEnd_2238408 := by exact prefixLift 2238408
  have htrace : WordTrace (prefixWord ++ tailWord_2238408) baseStart_2238408 baseEnd_2238408 := by
    simpa [prefixWord, tailWord_2238408, baseEnd_2238408] using wordTrace_append hprefix tailTrace_2238408
  have hstable : (prefixWord ++ tailWord_2238408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238408).length < 2 ^ (prefixWord ++ tailWord_2238408).sum := by decide
  have hdescent : baseEnd_2238408 < baseStart_2238408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238421 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 8]
def baseStart_2238421 : Nat := 118140960795 + 2238421 * 2 ^ 59
def prefixEnd_2238421 : Nat := 4983230072969 + 3 ^ 40 * 2238421 * 2
def baseEnd_2238421 : Nat := 127709542235321322360355

theorem tailTrace_2238421 : CollatzResearch.WordTrace tailWord_2238421 prefixEnd_2238421 127709542235321322360355 := by
  unfold tailWord_2238421
  simp only [CollatzResearch.WordTrace]
  refine ⟨81641921023590483716099117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54427947349060322477399411 81641921023590483716099117)
  ·
    refine ⟨30615720383846431393537169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81641921023590483716099117 30615720383846431393537169)
    ·
      refine ⟨22961790287884823545152877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30615720383846431393537169 22961790287884823545152877)
      ·
        refine ⟨8610671357956808829432329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22961790287884823545152877 8610671357956808829432329)
        ·
          refine ⟨6458003518467606622074247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8610671357956808829432329 6458003518467606622074247)
          ·
            refine ⟨9687005277701409933111371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6458003518467606622074247 9687005277701409933111371)
            ·
              refine ⟨14530507916552114899667057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9687005277701409933111371 14530507916552114899667057)
              ·
                refine ⟨10897880937414086174750293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14530507916552114899667057 10897880937414086174750293)
                ·
                  refine ⟨127709542235321322360355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10897880937414086174750293 127709542235321322360355)
                  ·
                    rfl

theorem cell23_2238421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_2238421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238421 prefixEnd_2238421 := by exact prefixLift 2238421
  have htrace : WordTrace (prefixWord ++ tailWord_2238421) baseStart_2238421 baseEnd_2238421 := by
    simpa [prefixWord, tailWord_2238421, baseEnd_2238421] using wordTrace_append hprefix tailTrace_2238421
  have hstable : (prefixWord ++ tailWord_2238421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238421).length < 2 ^ (prefixWord ++ tailWord_2238421).sum := by decide
  have hdescent : baseEnd_2238421 < baseStart_2238421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238442 : List Nat := [3, 1, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_2238442 : Nat := 118140960795 + 2238442 * 2 ^ 59
def prefixEnd_2238442 : Nat := 4983230072969 + 3 ^ 40 * 2238442 * 2
def baseEnd_2238442 : Nat := 383132221070545439693533

theorem tailTrace_2238442 : CollatzResearch.WordTrace tailWord_2238442 prefixEnd_2238442 383132221070545439693533 := by
  unfold tailWord_2238442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20410671739128601075653395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54428457971009602868409053 20410671739128601075653395)
  ·
    refine ⟨30616007608692901613480093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20410671739128601075653395 30616007608692901613480093)
    ·
      refine ⟨11481002853259838105055035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30616007608692901613480093 11481002853259838105055035)
      ·
        refine ⟨17221504279889757157582553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11481002853259838105055035 17221504279889757157582553)
        ·
          refine ⟨12916128209917317868186915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17221504279889757157582553 12916128209917317868186915)
          ·
            refine ⟨19374192314875976802280373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12916128209917317868186915 19374192314875976802280373)
            ·
              refine ⟨1816330529519622825213785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19374192314875976802280373 1816330529519622825213785)
              ·
                refine ⟨1362247897139717118910339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816330529519622825213785 1362247897139717118910339)
                ·
                  refine ⟨2043371845709575678365509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362247897139717118910339 2043371845709575678365509)
                  ·
                    refine ⟨383132221070545439693533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2043371845709575678365509 383132221070545439693533)
                    ·
                      rfl

theorem cell23_2238442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_2238442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238442 prefixEnd_2238442 := by exact prefixLift 2238442
  have htrace : WordTrace (prefixWord ++ tailWord_2238442) baseStart_2238442 baseEnd_2238442 := by
    simpa [prefixWord, tailWord_2238442, baseEnd_2238442] using wordTrace_append hprefix tailTrace_2238442
  have hstable : (prefixWord ++ tailWord_2238442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238442).length < 2 ^ (prefixWord ++ tailWord_2238442).sum := by decide
  have hdescent : baseEnd_2238442 < baseStart_2238442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238475 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 2, 3, 2]
def baseStart_2238475 : Nat := 118140960795 + 2238475 * 2 ^ 59
def prefixEnd_2238475 : Nat := 4983230072969 + 3 ^ 40 * 2238475 * 2
def baseEnd_2238475 : Nat := 1149413608073234689967947

theorem tailTrace_2238475 : CollatzResearch.WordTrace tailWord_2238475 prefixEnd_2238475 1149413608073234689967947 := by
  unfold tailWord_2238475
  simp only [CollatzResearch.WordTrace]
  refine ⟨81643890565394850938564879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54429260376929900625709919 81643890565394850938564879)
  ·
    refine ⟨122465835848092276407847319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81643890565394850938564879 122465835848092276407847319)
    ·
      refine ⟨183698753772138414611770979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122465835848092276407847319 183698753772138414611770979)
      ·
        refine ⟨275548130658207621917656469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183698753772138414611770979 275548130658207621917656469)
        ·
          refine ⟨12916318624603482277390147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 275548130658207621917656469 12916318624603482277390147)
          ·
            refine ⟨19374477936905223416085221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12916318624603482277390147 19374477936905223416085221)
            ·
              refine ⟨3632714613169729390515979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19374477936905223416085221 3632714613169729390515979)
              ·
                refine ⟨5449071919754594085773969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632714613169729390515979 5449071919754594085773969)
                ·
                  refine ⟨4086803939815945564330477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5449071919754594085773969 4086803939815945564330477)
                  ·
                    refine ⟨1532551477430979586623929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4086803939815945564330477 1532551477430979586623929)
                    ·
                      refine ⟨1149413608073234689967947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532551477430979586623929 1149413608073234689967947)
                      ·
                        rfl

theorem cell23_2238475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3, 2].length) (baseStart_2238475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238475 prefixEnd_2238475 := by exact prefixLift 2238475
  have htrace : WordTrace (prefixWord ++ tailWord_2238475) baseStart_2238475 baseEnd_2238475 := by
    simpa [prefixWord, tailWord_2238475, baseEnd_2238475] using wordTrace_append hprefix tailTrace_2238475
  have hstable : (prefixWord ++ tailWord_2238475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238475).length < 2 ^ (prefixWord ++ tailWord_2238475).sum := by decide
  have hdescent : baseEnd_2238475 < baseStart_2238475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238491 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5]
def baseStart_2238491 : Nat := 118140960795 + 2238491 * 2 ^ 59
def prefixEnd_2238491 : Nat := 4983230072969 + 3 ^ 40 * 2238491 * 2
def baseEnd_2238491 : Nat := 1149421823763706627367873

theorem tailTrace_2238491 : CollatzResearch.WordTrace tailWord_2238491 prefixEnd_2238491 1149421823763706627367873 := by
  unfold tailWord_2238491
  simp only [CollatzResearch.WordTrace]
  refine ⟨81644474133336885671147327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54429649422224590447431551 81644474133336885671147327)
  ·
    refine ⟨122466711200005328506720991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81644474133336885671147327 122466711200005328506720991)
    ·
      refine ⟨183700066800007992760081487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122466711200005328506720991 183700066800007992760081487)
      ·
        refine ⟨275550100200011989140122231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183700066800007992760081487 275550100200011989140122231)
        ·
          refine ⟨413325150300017983710183347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275550100200011989140122231 413325150300017983710183347)
          ·
            refine ⟨619987725450026975565275021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413325150300017983710183347 619987725450026975565275021)
            ·
              refine ⟨232495397043760115836978133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 619987725450026975565275021 232495397043760115836978133)
              ·
                refine ⟨5449110868213127714929175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232495397043760115836978133 5449110868213127714929175)
                ·
                  refine ⟨8173666302319691572393763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5449110868213127714929175 8173666302319691572393763)
                  ·
                    refine ⟨12260499453479537358590645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8173666302319691572393763 12260499453479537358590645)
                    ·
                      refine ⟨1149421823763706627367873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12260499453479537358590645 1149421823763706627367873)
                      ·
                        rfl

theorem cell23_2238491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5].length) (baseStart_2238491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238491 prefixEnd_2238491 := by exact prefixLift 2238491
  have htrace : WordTrace (prefixWord ++ tailWord_2238491) baseStart_2238491 baseEnd_2238491 := by
    simpa [prefixWord, tailWord_2238491, baseEnd_2238491] using wordTrace_append hprefix tailTrace_2238491
  have hstable : (prefixWord ++ tailWord_2238491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238491).length < 2 ^ (prefixWord ++ tailWord_2238491).sum := by decide
  have hdescent : baseEnd_2238491 < baseStart_2238491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238525 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2238525 : Nat := 118140960795 + 2238525 * 2 ^ 59
def prefixEnd_2238525 : Nat := 4983230072969 + 3 ^ 40 * 2238525 * 2
def baseEnd_2238525 : Nat := 1149439282105959494342717

theorem tailTrace_2238525 : CollatzResearch.WordTrace tailWord_2238525 prefixEnd_2238525 1149439282105959494342717 := by
  unfold tailWord_2238525
  simp only [CollatzResearch.WordTrace]
  refine ⟨81645714215213709477885029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54430476143475806318590019 81645714215213709477885029)
  ·
    refine ⟨15308571415352570527103443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81645714215213709477885029 15308571415352570527103443)
    ·
      refine ⟨22962857123028855790655165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15308571415352570527103443 22962857123028855790655165)
      ·
        refine ⟨8611071421135820921495687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22962857123028855790655165 8611071421135820921495687)
        ·
          refine ⟨12916607131703731382243531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8611071421135820921495687 12916607131703731382243531)
          ·
            refine ⟨19374910697555597073365297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12916607131703731382243531 19374910697555597073365297)
            ·
              refine ⟨14531183023166697805023973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19374910697555597073365297 14531183023166697805023973)
              ·
                refine ⟨2724596816843755838441995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14531183023166697805023973 2724596816843755838441995)
                ·
                  refine ⟨4086895225265633757662993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724596816843755838441995 4086895225265633757662993)
                  ·
                    refine ⟨3065171418949225318247245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4086895225265633757662993 3065171418949225318247245)
                    ·
                      refine ⟨1149439282105959494342717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3065171418949225318247245 1149439282105959494342717)
                      ·
                        rfl

theorem cell23_2238525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2238525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238525 prefixEnd_2238525 := by exact prefixLift 2238525
  have htrace : WordTrace (prefixWord ++ tailWord_2238525) baseStart_2238525 baseEnd_2238525 := by
    simpa [prefixWord, tailWord_2238525, baseEnd_2238525] using wordTrace_append hprefix tailTrace_2238525
  have hstable : (prefixWord ++ tailWord_2238525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238525).length < 2 ^ (prefixWord ++ tailWord_2238525).sum := by decide
  have hdescent : baseEnd_2238525 < baseStart_2238525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238526 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_2238526 : Nat := 118140960795 + 2238526 * 2 ^ 59
def prefixEnd_2238526 : Nat := 4983230072969 + 3 ^ 40 * 2238526 * 2
def baseEnd_2238526 : Nat := 1149439795586613990430213

theorem tailTrace_2238526 : CollatzResearch.WordTrace tailWord_2238526 prefixEnd_2238526 1149439795586613990430213 := by
  unfold tailWord_2238526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10205718836026260831083929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54430500458806724432447621 10205718836026260831083929)
  ·
    refine ⟨7654289127019695623312947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10205718836026260831083929 7654289127019695623312947)
    ·
      refine ⟨11481433690529543434969421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7654289127019695623312947 11481433690529543434969421)
      ·
        refine ⟨4305537633948578788113533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11481433690529543434969421 4305537633948578788113533)
        ·
          refine ⟨1614576612730717045542575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4305537633948578788113533 1614576612730717045542575)
          ·
            refine ⟨2421864919096075568313863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614576612730717045542575 2421864919096075568313863)
            ·
              refine ⟨3632797378644113352470795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421864919096075568313863 3632797378644113352470795)
              ·
                refine ⟨5449196067966170028706193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632797378644113352470795 5449196067966170028706193)
                ·
                  refine ⟨4086897050974627521529645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5449196067966170028706193 4086897050974627521529645)
                  ·
                    refine ⟨1532586394115485320573617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4086897050974627521529645 1532586394115485320573617)
                    ·
                      refine ⟨1149439795586613990430213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532586394115485320573617 1149439795586613990430213)
                      ·
                        rfl

theorem cell23_2238526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_2238526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238526 prefixEnd_2238526 := by exact prefixLift 2238526
  have htrace : WordTrace (prefixWord ++ tailWord_2238526) baseStart_2238526 baseEnd_2238526 := by
    simpa [prefixWord, tailWord_2238526, baseEnd_2238526] using wordTrace_append hprefix tailTrace_2238526
  have hstable : (prefixWord ++ tailWord_2238526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238526).length < 2 ^ (prefixWord ++ tailWord_2238526).sum := by decide
  have hdescent : baseEnd_2238526 < baseStart_2238526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238528 : List Nat := [2, 1, 1, 2, 2, 5, 3, 7]
def baseStart_2238528 : Nat := 118140960795 + 2238528 * 2 ^ 59
def prefixEnd_2238528 : Nat := 4983230072969 + 3 ^ 40 * 2238528 * 2
def baseEnd_2238528 : Nat := 42571882316589740096489

theorem tailTrace_2238528 : CollatzResearch.WordTrace tailWord_2238528 prefixEnd_2238528 42571882316589740096489 := by
  unfold tailWord_2238528
  simp only [CollatzResearch.WordTrace]
  refine ⟨40822911817101420495122119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54430549089468560660162825 40822911817101420495122119)
  ·
    refine ⟨61234367725652130742683179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40822911817101420495122119 61234367725652130742683179)
    ·
      refine ⟨91851551588478196114024769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61234367725652130742683179 91851551588478196114024769)
      ·
        refine ⟨68888663691358647085518577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91851551588478196114024769 68888663691358647085518577)
        ·
          refine ⟨51666497768518985314138933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68888663691358647085518577 51666497768518985314138933)
          ·
            refine ⟨4843734165798654873200525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51666497768518985314138933 4843734165798654873200525)
            ·
              refine ⟨1816400312174495577450197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4843734165798654873200525 1816400312174495577450197)
              ·
                refine ⟨42571882316589740096489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1816400312174495577450197 42571882316589740096489)
                ·
                  rfl

theorem cell23_2238528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 7].length) (baseStart_2238528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238528 prefixEnd_2238528 := by exact prefixLift 2238528
  have htrace : WordTrace (prefixWord ++ tailWord_2238528) baseStart_2238528 baseEnd_2238528 := by
    simpa [prefixWord, tailWord_2238528, baseEnd_2238528] using wordTrace_append hprefix tailTrace_2238528
  have hstable : (prefixWord ++ tailWord_2238528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238528).length < 2 ^ (prefixWord ++ tailWord_2238528).sum := by decide
  have hdescent : baseEnd_2238528 < baseStart_2238528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238542 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_2238542 : Nat := 118140960795 + 2238542 * 2 ^ 59
def prefixEnd_2238542 : Nat := 4983230072969 + 3 ^ 40 * 2238542 * 2
def baseEnd_2238542 : Nat := 1149448011277085927830139

theorem tailTrace_2238542 : CollatzResearch.WordTrace tailWord_2238542 prefixEnd_2238542 1149448011277085927830139 := by
  unfold tailWord_2238542
  simp only [CollatzResearch.WordTrace]
  refine ⟨10205791782019015172656735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54430889504101414254169253 10205791782019015172656735)
  ·
    refine ⟨15308687673028522758985103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10205791782019015172656735 15308687673028522758985103)
    ·
      refine ⟨22963031509542784138477655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15308687673028522758985103 22963031509542784138477655)
      ·
        refine ⟨34444547264314176207716483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22963031509542784138477655 34444547264314176207716483)
        ·
          refine ⟨51666820896471264311574725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34444547264314176207716483 51666820896471264311574725)
          ·
            refine ⟨9687528918088362058420261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51666820896471264311574725 9687528918088362058420261)
            ·
              refine ⟨1816411672141567885953799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9687528918088362058420261 1816411672141567885953799)
              ·
                refine ⟨2724617508212351828930699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816411672141567885953799 2724617508212351828930699)
                ·
                  refine ⟨4086926262318527743396049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724617508212351828930699 4086926262318527743396049)
                  ·
                    refine ⟨3065194696738895807547037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4086926262318527743396049 3065194696738895807547037)
                    ·
                      refine ⟨1149448011277085927830139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3065194696738895807547037 1149448011277085927830139)
                      ·
                        rfl

theorem cell23_2238542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_2238542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238542 prefixEnd_2238542 := by exact prefixLift 2238542
  have htrace : WordTrace (prefixWord ++ tailWord_2238542) baseStart_2238542 baseEnd_2238542 := by
    simpa [prefixWord, tailWord_2238542, baseEnd_2238542] using wordTrace_append hprefix tailTrace_2238542
  have hstable : (prefixWord ++ tailWord_2238542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238542).length < 2 ^ (prefixWord ++ tailWord_2238542).sum := by decide
  have hdescent : baseEnd_2238542 < baseStart_2238542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238611 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9]
def baseStart_2238611 : Nat := 118140960795 + 2238611 * 2 ^ 59
def prefixEnd_2238611 : Nat := 4983230072969 + 3 ^ 40 * 2238611 * 2
def baseEnd_2238611 : Nat := 1149483441442246157867321

theorem tailTrace_2238611 : CollatzResearch.WordTrace tailWord_2238611 prefixEnd_2238611 1149483441442246157867321 := by
  unfold tailWord_2238611
  simp only [CollatzResearch.WordTrace]
  refine ⟨81648850892902146165515687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54432567261934764110343791 81648850892902146165515687)
  ·
    refine ⟨122473276339353219248273531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81648850892902146165515687 122473276339353219248273531)
    ·
      refine ⟨183709914509029828872410297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122473276339353219248273531 183709914509029828872410297)
      ·
        refine ⟨137782435881772371654307723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183709914509029828872410297 137782435881772371654307723)
        ·
          refine ⟨206673653822658557481461585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137782435881772371654307723 206673653822658557481461585)
          ·
            refine ⟨155005240366993918111096189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206673653822658557481461585 155005240366993918111096189)
            ·
              refine ⟨58126965137622719291661071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155005240366993918111096189 58126965137622719291661071)
              ·
                refine ⟨87190447706434078937491607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58126965137622719291661071 87190447706434078937491607)
                ·
                  refine ⟨130785671559651118406237411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87190447706434078937491607 130785671559651118406237411)
                  ·
                    refine ⟨196178507339476677609356117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130785671559651118406237411 196178507339476677609356117)
                    ·
                      refine ⟨1149483441442246157867321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 196178507339476677609356117 1149483441442246157867321)
                      ·
                        rfl

theorem cell23_2238611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_2238611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238611 prefixEnd_2238611 := by exact prefixLift 2238611
  have htrace : WordTrace (prefixWord ++ tailWord_2238611) baseStart_2238611 baseEnd_2238611 := by
    simpa [prefixWord, tailWord_2238611, baseEnd_2238611] using wordTrace_append hprefix tailTrace_2238611
  have hstable : (prefixWord ++ tailWord_2238611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238611).length < 2 ^ (prefixWord ++ tailWord_2238611).sum := by decide
  have hdescent : baseEnd_2238611 < baseStart_2238611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238826 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2238826 : Nat := 118140960795 + 2238826 * 2 ^ 59
def prefixEnd_2238826 : Nat := 4983230072969 + 3 ^ 40 * 2238826 * 2
def baseEnd_2238826 : Nat := 1149593839782962816678833

theorem tailTrace_2238826 : CollatzResearch.WordTrace tailWord_2238826 prefixEnd_2238826 1149593839782962816678833 := by
  unfold tailWord_2238826
  simp only [CollatzResearch.WordTrace]
  refine ⟨20414173146780809471148083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54437795058082158589728221 20414173146780809471148083)
  ·
    refine ⟨30621259720171214206722125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20414173146780809471148083 30621259720171214206722125)
    ·
      refine ⟨11482972395064205327520797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30621259720171214206722125 11482972395064205327520797)
      ·
        refine ⟨4306114648149076997820299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11482972395064205327520797 4306114648149076997820299)
        ·
          refine ⟨6459171972223615496730449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306114648149076997820299 6459171972223615496730449)
          ·
            refine ⟨4844378979167711622547837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6459171972223615496730449 4844378979167711622547837)
            ·
              refine ⟨1816642117187891858455439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4844378979167711622547837 1816642117187891858455439)
              ·
                refine ⟨2724963175781837787683159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816642117187891858455439 2724963175781837787683159)
                ·
                  refine ⟨4087444763672756681524739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724963175781837787683159 4087444763672756681524739)
                  ·
                    refine ⟨6131167145509135022287109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4087444763672756681524739 6131167145509135022287109)
                    ·
                      refine ⟨1149593839782962816678833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6131167145509135022287109 1149593839782962816678833)
                      ·
                        rfl

theorem cell23_2238826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2238826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238826 prefixEnd_2238826 := by exact prefixLift 2238826
  have htrace : WordTrace (prefixWord ++ tailWord_2238826) baseStart_2238826 baseEnd_2238826 := by
    simpa [prefixWord, tailWord_2238826, baseEnd_2238826] using wordTrace_append hprefix tailTrace_2238826
  have hstable : (prefixWord ++ tailWord_2238826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238826).length < 2 ^ (prefixWord ++ tailWord_2238826).sum := by decide
  have hdescent : baseEnd_2238826 < baseStart_2238826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238843 : List Nat := [1, 1, 1, 1, 1, 7, 4, 2, 1, 2, 2]
def baseStart_2238843 : Nat := 118140960795 + 2238843 * 2 ^ 59
def prefixEnd_2238843 : Nat := 4983230072969 + 3 ^ 40 * 2238843 * 2
def baseEnd_2238843 : Nat := 1149602568954089250166255

theorem tailTrace_2238843 : CollatzResearch.WordTrace tailWord_2238843 prefixEnd_2238843 1149602568954089250166255 := by
  unfold tailWord_2238843
  simp only [CollatzResearch.WordTrace]
  refine ⟨81657312628061649787961183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54438208418707766525307455 81657312628061649787961183)
  ·
    refine ⟨122485968942092474681941775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81657312628061649787961183 122485968942092474681941775)
    ·
      refine ⟨183728953413138712022912663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122485968942092474681941775 183728953413138712022912663)
      ·
        refine ⟨275593430119708068034368995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183728953413138712022912663 275593430119708068034368995)
        ·
          refine ⟨413390145179562102051553493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275593430119708068034368995 413390145179562102051553493)
          ·
            refine ⟨9688831527645986766833285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 413390145179562102051553493 9688831527645986766833285)
            ·
              refine ⟨1816655911433622518781241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9688831527645986766833285 1816655911433622518781241)
              ·
                refine ⟨1362491933575216889085931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816655911433622518781241 1362491933575216889085931)
                ·
                  refine ⟨2043737900362825333628897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362491933575216889085931 2043737900362825333628897)
                  ·
                    refine ⟨1532803425272119000221673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2043737900362825333628897 1532803425272119000221673)
                    ·
                      refine ⟨1149602568954089250166255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532803425272119000221673 1149602568954089250166255)
                      ·
                        rfl

theorem cell23_2238843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 2, 2].length) (baseStart_2238843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238843 prefixEnd_2238843 := by exact prefixLift 2238843
  have htrace : WordTrace (prefixWord ++ tailWord_2238843) baseStart_2238843 baseEnd_2238843 := by
    simpa [prefixWord, tailWord_2238843, baseEnd_2238843] using wordTrace_append hprefix tailTrace_2238843
  have hstable : (prefixWord ++ tailWord_2238843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238843).length < 2 ^ (prefixWord ++ tailWord_2238843).sum := by decide
  have hdescent : baseEnd_2238843 < baseStart_2238843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238845 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_2238845 : Nat := 118140960795 + 2238845 * 2 ^ 59
def prefixEnd_2238845 : Nat := 4983230072969 + 3 ^ 40 * 2238845 * 2
def baseEnd_2238845 : Nat := 383201198638466080780415

theorem tailTrace_2238845 : CollatzResearch.WordTrace tailWord_2238845 prefixEnd_2238845 383201198638466080780415 := by
  unfold tailWord_2238845
  simp only [CollatzResearch.WordTrace]
  refine ⟨81657385574054404129533989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54438257049369602753022659 81657385574054404129533989)
  ·
    refine ⟨15310759795135200774287623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81657385574054404129533989 15310759795135200774287623)
    ·
      refine ⟨22966139692702801161431435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15310759795135200774287623 22966139692702801161431435)
      ·
        refine ⟨34449209539054201742147153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22966139692702801161431435 34449209539054201742147153)
        ·
          refine ⟨25836907154290651306610365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34449209539054201742147153 25836907154290651306610365)
          ·
            refine ⟨9688840182858994239978887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25836907154290651306610365 9688840182858994239978887)
            ·
              refine ⟨14533260274288491359968331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9688840182858994239978887 14533260274288491359968331)
              ·
                refine ⟨21799890411432737039952497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14533260274288491359968331 21799890411432737039952497)
                ·
                  refine ⟨16349917808574552779964373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21799890411432737039952497 16349917808574552779964373)
                  ·
                    refine ⟨383201198638466080780415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16349917808574552779964373 383201198638466080780415)
                    ·
                      rfl

theorem cell23_2238845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_2238845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238845 prefixEnd_2238845 := by exact prefixLift 2238845
  have htrace : WordTrace (prefixWord ++ tailWord_2238845) baseStart_2238845 baseEnd_2238845 := by
    simpa [prefixWord, tailWord_2238845, baseEnd_2238845] using wordTrace_append hprefix tailTrace_2238845
  have hstable : (prefixWord ++ tailWord_2238845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238845).length < 2 ^ (prefixWord ++ tailWord_2238845).sum := by decide
  have hdescent : baseEnd_2238845 < baseStart_2238845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238859 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 3]
def baseStart_2238859 : Nat := 118140960795 + 2238859 * 2 ^ 59
def prefixEnd_2238859 : Nat := 4983230072969 + 3 ^ 40 * 2238859 * 2
def baseEnd_2238859 : Nat := 1149610784644561187566181

theorem tailTrace_2238859 : CollatzResearch.WordTrace tailWord_2238859 prefixEnd_2238859 1149610784644561187566181 := by
  unfold tailWord_2238859
  simp only [CollatzResearch.WordTrace]
  refine ⟨81657896196003684520543631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54438597464002456347029087 81657896196003684520543631)
  ·
    refine ⟨122486844294005526780815447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81657896196003684520543631 122486844294005526780815447)
    ·
      refine ⟨183730266441008290171223171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122486844294005526780815447 183730266441008290171223171)
      ·
        refine ⟨275595399661512435256834757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183730266441008290171223171 275595399661512435256834757)
        ·
          refine ⟨51674137436533581610656517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 275595399661512435256834757 51674137436533581610656517)
          ·
            refine ⟨9688900769350046551998097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51674137436533581610656517 9688900769350046551998097)
            ·
              refine ⟨7266675577012534913998573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9688900769350046551998097 7266675577012534913998573)
              ·
                refine ⟨2725003341379700592749465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7266675577012534913998573 2725003341379700592749465)
                ·
                  refine ⟨2043752506034775444562099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725003341379700592749465 2043752506034775444562099)
                  ·
                    refine ⟨3065628759052163166843149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2043752506034775444562099 3065628759052163166843149)
                    ·
                      refine ⟨1149610784644561187566181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3065628759052163166843149 1149610784644561187566181)
                      ·
                        rfl

theorem cell23_2238859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 3].length) (baseStart_2238859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238859 prefixEnd_2238859 := by exact prefixLift 2238859
  have htrace : WordTrace (prefixWord ++ tailWord_2238859) baseStart_2238859 baseEnd_2238859 := by
    simpa [prefixWord, tailWord_2238859, baseEnd_2238859] using wordTrace_append hprefix tailTrace_2238859
  have hstable : (prefixWord ++ tailWord_2238859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238859).length < 2 ^ (prefixWord ++ tailWord_2238859).sum := by decide
  have hdescent : baseEnd_2238859 < baseStart_2238859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238869 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_2238869 : Nat := 118140960795 + 2238869 * 2 ^ 59
def prefixEnd_2238869 : Nat := 4983230072969 + 3 ^ 40 * 2238869 * 2
def baseEnd_2238869 : Nat := 1149615919451106148441135

theorem tailTrace_2238869 : CollatzResearch.WordTrace tailWord_2238869 prefixEnd_2238869 1149615919451106148441135 := by
  unfold tailWord_2238869
  simp only [CollatzResearch.WordTrace]
  refine ⟨81658260925967456228407661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54438840617311637485605107 81658260925967456228407661)
  ·
    refine ⟨30621847847237796085652873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81658260925967456228407661 30621847847237796085652873)
    ·
      refine ⟨22966385885428347064239655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30621847847237796085652873 22966385885428347064239655)
      ·
        refine ⟨34449578828142520596359483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22966385885428347064239655 34449578828142520596359483)
        ·
          refine ⟨51674368242213780894539225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34449578828142520596359483 51674368242213780894539225)
          ·
            refine ⟨38755776181660335670904419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51674368242213780894539225 38755776181660335670904419)
            ·
              refine ⟨58133664272490503506356629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38755776181660335670904419 58133664272490503506356629)
              ·
                refine ⟨2725015512772992351860467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58133664272490503506356629 2725015512772992351860467)
                ·
                  refine ⟨4087523269159488527790701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725015512772992351860467 4087523269159488527790701)
                  ·
                    refine ⟨1532821225934808197921513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4087523269159488527790701 1532821225934808197921513)
                    ·
                      refine ⟨1149615919451106148441135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1532821225934808197921513 1149615919451106148441135)
                      ·
                        rfl

theorem cell23_2238869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_2238869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238869 prefixEnd_2238869 := by exact prefixLift 2238869
  have htrace : WordTrace (prefixWord ++ tailWord_2238869) baseStart_2238869 baseEnd_2238869 := by
    simpa [prefixWord, tailWord_2238869, baseEnd_2238869] using wordTrace_append hprefix tailTrace_2238869
  have hstable : (prefixWord ++ tailWord_2238869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238869).length < 2 ^ (prefixWord ++ tailWord_2238869).sum := by decide
  have hdescent : baseEnd_2238869 < baseStart_2238869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238885 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_2238885 : Nat := 118140960795 + 2238885 * 2 ^ 59
def prefixEnd_2238885 : Nat := 4983230072969 + 3 ^ 40 * 2238885 * 2
def baseEnd_2238885 : Nat := 1149624135141578085841061

theorem tailTrace_2238885 : CollatzResearch.WordTrace tailWord_2238885 prefixEnd_2238885 1149624135141578085841061 := by
  unfold tailWord_2238885
  simp only [CollatzResearch.WordTrace]
  refine ⟨81658844493909490960990109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54439229662606327307326739 81658844493909490960990109)
  ·
    refine ⟨30622066685216059110371291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81658844493909490960990109 30622066685216059110371291)
    ·
      refine ⟨45933100027824088665556937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30622066685216059110371291 45933100027824088665556937)
      ·
        refine ⟨34449825020868066499167703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45933100027824088665556937 34449825020868066499167703)
        ·
          refine ⟨51674737531302099748751555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34449825020868066499167703 51674737531302099748751555)
          ·
            refine ⟨77512106296953149623127333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51674737531302099748751555 77512106296953149623127333)
            ·
              refine ⟨14533519930678715554336375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77512106296953149623127333 14533519930678715554336375)
              ·
                refine ⟨21800279896018073331504563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14533519930678715554336375 21800279896018073331504563)
                ·
                  refine ⟨32700419844027109997256845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21800279896018073331504563 32700419844027109997256845)
                  ·
                    refine ⟨12262657441510166248971317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32700419844027109997256845 12262657441510166248971317)
                    ·
                      refine ⟨1149624135141578085841061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12262657441510166248971317 1149624135141578085841061)
                      ·
                        rfl

theorem cell23_2238885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_2238885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238885 prefixEnd_2238885 := by exact prefixLift 2238885
  have htrace : WordTrace (prefixWord ++ tailWord_2238885) baseStart_2238885 baseEnd_2238885 := by
    simpa [prefixWord, tailWord_2238885, baseEnd_2238885] using wordTrace_append hprefix tailTrace_2238885
  have hstable : (prefixWord ++ tailWord_2238885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238885).length < 2 ^ (prefixWord ++ tailWord_2238885).sum := by decide
  have hdescent : baseEnd_2238885 < baseStart_2238885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238952 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2238952 : Nat := 118140960795 + 2238952 * 2 ^ 59
def prefixEnd_2238952 : Nat := 4983230072969 + 3 ^ 40 * 2238952 * 2
def baseEnd_2238952 : Nat := 383219512781809774567751

theorem tailTrace_2238952 : CollatzResearch.WordTrace tailWord_2238952 prefixEnd_2238952 383219512781809774567751 := by
  unfold tailWord_2238952
  simp only [CollatzResearch.WordTrace]
  refine ⟨40830644092333380701839555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54440858789777840935786073 40830644092333380701839555)
  ·
    refine ⟨61245966138500071052759333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40830644092333380701839555 61245966138500071052759333)
    ·
      refine ⟨11483618650968763322392375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61245966138500071052759333 11483618650968763322392375)
      ·
        refine ⟨17225427976453144983588563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11483618650968763322392375 17225427976453144983588563)
        ·
          refine ⟨25838141964679717475382845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17225427976453144983588563 25838141964679717475382845)
          ·
            refine ⟨9689303236754894053268567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25838141964679717475382845 9689303236754894053268567)
            ·
              refine ⟨14533954855132341079902851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9689303236754894053268567 14533954855132341079902851)
              ·
                refine ⟨21800932282698511619854277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14533954855132341079902851 21800932282698511619854277)
                ·
                  refine ⟨4087674803005970928722677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21800932282698511619854277 4087674803005970928722677)
                  ·
                    refine ⟨383219512781809774567751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4087674803005970928722677 383219512781809774567751)
                    ·
                      rfl

theorem cell23_2238952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2238952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238952 prefixEnd_2238952 := by exact prefixLift 2238952
  have htrace : WordTrace (prefixWord ++ tailWord_2238952) baseStart_2238952 baseEnd_2238952 := by
    simpa [prefixWord, tailWord_2238952, baseEnd_2238952] using wordTrace_append hprefix tailTrace_2238952
  have hstable : (prefixWord ++ tailWord_2238952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238952).length < 2 ^ (prefixWord ++ tailWord_2238952).sum := by decide
  have hdescent : baseEnd_2238952 < baseStart_2238952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238972 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_2238972 : Nat := 118140960795 + 2238972 * 2 ^ 59
def prefixEnd_2238972 : Nat := 4983230072969 + 3 ^ 40 * 2238972 * 2
def baseEnd_2238972 : Nat := 1149668807958519245453161

theorem tailTrace_2238972 : CollatzResearch.WordTrace tailWord_2238972 prefixEnd_2238972 1149668807958519245453161 := by
  unfold tailWord_2238972
  simp only [CollatzResearch.WordTrace]
  refine ⟨40831008822297152409703585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54441345096396203212938113 40831008822297152409703585)
  ·
    refine ⟨30623256616722864307277689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40831008822297152409703585 30623256616722864307277689)
    ·
      refine ⟨22967442462542148230458267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30623256616722864307277689 22967442462542148230458267)
      ·
        refine ⟨34451163693813222345687401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22967442462542148230458267 34451163693813222345687401)
        ·
          refine ⟨25838372770359916759265551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34451163693813222345687401 25838372770359916759265551)
          ·
            refine ⟨38757559155539875138898327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25838372770359916759265551 38757559155539875138898327)
            ·
              refine ⟨58136338733309812708347491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38757559155539875138898327 58136338733309812708347491)
              ·
                refine ⟨87204508099964719062521237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58136338733309812708347491 87204508099964719062521237)
                ·
                  refine ⟨4087711317185846206055683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87204508099964719062521237 4087711317185846206055683)
                  ·
                    refine ⟨6131566975778769309083525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4087711317185846206055683 6131566975778769309083525)
                    ·
                      refine ⟨1149668807958519245453161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6131566975778769309083525 1149668807958519245453161)
                      ·
                        rfl

theorem cell23_2238972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_2238972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2238972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2238972 prefixEnd_2238972 := by exact prefixLift 2238972
  have htrace : WordTrace (prefixWord ++ tailWord_2238972) baseStart_2238972 baseEnd_2238972 := by
    simpa [prefixWord, tailWord_2238972, baseEnd_2238972] using wordTrace_append hprefix tailTrace_2238972
  have hstable : (prefixWord ++ tailWord_2238972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238972).length < 2 ^ (prefixWord ++ tailWord_2238972).sum := by decide
  have hdescent : baseEnd_2238972 < baseStart_2238972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239009 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2239009 : Nat := 118140960795 + 2239009 * 2 ^ 59
def prefixEnd_2239009 : Nat := 4983230072969 + 3 ^ 40 * 2239009 * 2
def baseEnd_2239009 : Nat := 1149687806742735600690491

theorem tailTrace_2239009 : CollatzResearch.WordTrace tailWord_2239009 prefixEnd_2239009 1149687806742735600690491 := by
  unfold tailWord_2239009
  simp only [CollatzResearch.WordTrace]
  refine ⟨81663367145460260138504081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54442244763640173425669387 81663367145460260138504081)
  ·
    refine ⟨61247525359095195103878061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81663367145460260138504081 61247525359095195103878061)
    ·
      refine ⟨22967822009660698163954273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61247525359095195103878061 22967822009660698163954273)
      ·
        refine ⟨17225866507245523622965705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22967822009660698163954273 17225866507245523622965705)
        ·
          refine ⟨12919399880434142717224279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17225866507245523622965705 12919399880434142717224279)
          ·
            refine ⟨19379099820651214075836419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12919399880434142717224279 19379099820651214075836419)
            ·
              refine ⟨29068649730976821113754629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19379099820651214075836419 29068649730976821113754629)
              ·
                refine ⟨5450371824558153958828993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29068649730976821113754629 5450371824558153958828993)
                ·
                  refine ⟨4087778868418615469121745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5450371824558153958828993 4087778868418615469121745)
                  ·
                    refine ⟨3065834151313961601841309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4087778868418615469121745 3065834151313961601841309)
                    ·
                      refine ⟨1149687806742735600690491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3065834151313961601841309 1149687806742735600690491)
                      ·
                        rfl

theorem cell23_2239009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2239009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239009 prefixEnd_2239009 := by exact prefixLift 2239009
  have htrace : WordTrace (prefixWord ++ tailWord_2239009) baseStart_2239009 baseEnd_2239009 := by
    simpa [prefixWord, tailWord_2239009, baseEnd_2239009] using wordTrace_append hprefix tailTrace_2239009
  have hstable : (prefixWord ++ tailWord_2239009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239009).length < 2 ^ (prefixWord ++ tailWord_2239009).sum := by decide
  have hdescent : baseEnd_2239009 < baseStart_2239009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239072 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 3, 6]
def baseStart_2239072 : Nat := 118140960795 + 2239072 * 2 ^ 59
def prefixEnd_2239072 : Nat := 4983230072969 + 3 ^ 40 * 2239072 * 2
def baseEnd_2239072 : Nat := 383240052007989618067567

theorem tailTrace_2239072 : CollatzResearch.WordTrace tailWord_2239072 prefixEnd_2239072 383240052007989618067567 := by
  unfold tailWord_2239072
  simp only [CollatzResearch.WordTrace]
  refine ⟨40832832472116010949023735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54443776629488014598698313 40832832472116010949023735)
  ·
    refine ⟨61249248708174016423535603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40832832472116010949023735 61249248708174016423535603)
    ·
      refine ⟨91873873062261024635303405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61249248708174016423535603 91873873062261024635303405)
      ·
        refine ⟨34452702398347884238238777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91873873062261024635303405 34452702398347884238238777)
        ·
          refine ⟨25839526798760913178679083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34452702398347884238238777 25839526798760913178679083)
          ·
            refine ⟨38759290198141369768018625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25839526798760913178679083 38759290198141369768018625)
            ·
              refine ⟨29069467648606027326013969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38759290198141369768018625 29069467648606027326013969)
              ·
                refine ⟨21802100736454520494510477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29069467648606027326013969 21802100736454520494510477)
                ·
                  refine ⟨8175787776170445185441429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21802100736454520494510477 8175787776170445185441429)
                  ·
                    refine ⟨383240052007989618067567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8175787776170445185441429 383240052007989618067567)
                    ·
                      rfl

theorem cell23_2239072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_2239072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239072 prefixEnd_2239072 := by exact prefixLift 2239072
  have htrace : WordTrace (prefixWord ++ tailWord_2239072) baseStart_2239072 baseEnd_2239072 := by
    simpa [prefixWord, tailWord_2239072, baseEnd_2239072] using wordTrace_append hprefix tailTrace_2239072
  have hstable : (prefixWord ++ tailWord_2239072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239072).length < 2 ^ (prefixWord ++ tailWord_2239072).sum := by decide
  have hdescent : baseEnd_2239072 < baseStart_2239072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239073 : List Nat := [1, 2, 3, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_2239073 : Nat := 118140960795 + 2239073 * 2 ^ 59
def prefixEnd_2239073 : Nat := 4983230072969 + 3 ^ 40 * 2239073 * 2
def baseEnd_2239073 : Nat := 1149720669504623350290197

theorem tailTrace_2239073 : CollatzResearch.WordTrace tailWord_2239073 prefixEnd_2239073 1149720669504623350290197 := by
  unfold tailWord_2239073
  simp only [CollatzResearch.WordTrace]
  refine ⟨81665701417228399068833873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54443800944818932712555915 81665701417228399068833873)
  ·
    refine ⟨61249276062921299301625405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81665701417228399068833873 61249276062921299301625405)
    ·
      refine ⟨22968478523595487238109527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61249276062921299301625405 22968478523595487238109527)
      ·
        refine ⟨34452717785393230857164291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22968478523595487238109527 34452717785393230857164291)
        ·
          refine ⟨51679076678089846285746437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34452717785393230857164291 51679076678089846285746437)
          ·
            refine ⟨9689826877141846178577457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51679076678089846285746437 9689826877141846178577457)
            ·
              refine ⟨7267370157856384633933093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9689826877141846178577457 7267370157856384633933093)
              ·
                refine ⟨1362631904598072118862455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7267370157856384633933093 1362631904598072118862455)
                ·
                  refine ⟨2043947856897108178293683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362631904598072118862455 2043947856897108178293683)
                  ·
                    refine ⟨3065921785345662267440525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2043947856897108178293683 3065921785345662267440525)
                    ·
                      refine ⟨1149720669504623350290197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3065921785345662267440525 1149720669504623350290197)
                      ·
                        rfl

theorem cell23_2239073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_2239073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239073 prefixEnd_2239073 := by exact prefixLift 2239073
  have htrace : WordTrace (prefixWord ++ tailWord_2239073) baseStart_2239073 baseEnd_2239073 := by
    simpa [prefixWord, tailWord_2239073, baseEnd_2239073] using wordTrace_append hprefix tailTrace_2239073
  have hstable : (prefixWord ++ tailWord_2239073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239073).length < 2 ^ (prefixWord ++ tailWord_2239073).sum := by decide
  have hdescent : baseEnd_2239073 < baseStart_2239073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239093 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2239093 : Nat := 118140960795 + 2239093 * 2 ^ 59
def prefixEnd_2239093 : Nat := 4983230072969 + 3 ^ 40 * 2239093 * 2
def baseEnd_2239093 : Nat := 383243646372571090680035

theorem tailTrace_2239093 : CollatzResearch.WordTrace tailWord_2239093 prefixEnd_2239093 383243646372571090680035 := by
  unfold tailWord_2239093
  simp only [CollatzResearch.WordTrace]
  refine ⟨81666430877155942484561933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54444287251437294989707955 81666430877155942484561933)
  ·
    refine ⟨30624911578933478431710725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81666430877155942484561933 30624911578933478431710725)
    ·
      refine ⟨5742170921050027205945761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30624911578933478431710725 5742170921050027205945761)
      ·
        refine ⟨4306628190787520404459321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5742170921050027205945761 4306628190787520404459321)
        ·
          refine ⟨3229971143090640303344491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4306628190787520404459321 3229971143090640303344491)
          ·
            refine ⟨4844956714635960455016737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229971143090640303344491 4844956714635960455016737)
            ·
              refine ⟨3633717535976970341262553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4844956714635960455016737 3633717535976970341262553)
              ·
                refine ⟨2725288151982727755946915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633717535976970341262553 2725288151982727755946915)
                ·
                  refine ⟨4087932227974091633920373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725288151982727755946915 4087932227974091633920373)
                  ·
                    refine ⟨383243646372571090680035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4087932227974091633920373 383243646372571090680035)
                    ·
                      rfl

theorem cell23_2239093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2239093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239093 prefixEnd_2239093 := by exact prefixLift 2239093
  have htrace : WordTrace (prefixWord ++ tailWord_2239093) baseStart_2239093 baseEnd_2239093 := by
    simpa [prefixWord, tailWord_2239093, baseEnd_2239093] using wordTrace_append hprefix tailTrace_2239093
  have hstable : (prefixWord ++ tailWord_2239093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239093).length < 2 ^ (prefixWord ++ tailWord_2239093).sum := by decide
  have hdescent : baseEnd_2239093 < baseStart_2239093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239150 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2239150 : Nat := 118140960795 + 2239150 * 2 ^ 59
def prefixEnd_2239150 : Nat := 4983230072969 + 3 ^ 40 * 2239150 * 2
def baseEnd_2239150 : Nat := 1149760207515019549027343

theorem tailTrace_2239150 : CollatzResearch.WordTrace tailWord_2239150 prefixEnd_2239150 1149760207515019549027343 := by
  unfold tailWord_2239150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10208563729743680152423363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54445673225299627479591269 10208563729743680152423363)
  ·
    refine ⟨15312845594615520228635045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10208563729743680152423363 15312845594615520228635045)
    ·
      refine ⟨2871158548990410042869071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15312845594615520228635045 2871158548990410042869071)
      ·
        refine ⟨4306737823485615064303607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871158548990410042869071 4306737823485615064303607)
        ·
          refine ⟨6460106735228422596455411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306737823485615064303607 6460106735228422596455411)
          ·
            refine ⟨9690160102842633894683117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460106735228422596455411 9690160102842633894683117)
            ·
              refine ⟨3633810038565987710506169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9690160102842633894683117 3633810038565987710506169)
              ·
                refine ⟨2725357528924490782879627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633810038565987710506169 2725357528924490782879627)
                ·
                  refine ⟨4088036293386736174319441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725357528924490782879627 4088036293386736174319441)
                  ·
                    refine ⟨3066027220040052130739581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4088036293386736174319441 3066027220040052130739581)
                    ·
                      refine ⟨1149760207515019549027343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066027220040052130739581 1149760207515019549027343)
                      ·
                        rfl

theorem cell23_2239150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2239150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239150 prefixEnd_2239150 := by exact prefixLift 2239150
  have htrace : WordTrace (prefixWord ++ tailWord_2239150) baseStart_2239150 baseEnd_2239150 := by
    simpa [prefixWord, tailWord_2239150, baseEnd_2239150] using wordTrace_append hprefix tailTrace_2239150
  have hstable : (prefixWord ++ tailWord_2239150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239150).length < 2 ^ (prefixWord ++ tailWord_2239150).sum := by decide
  have hdescent : baseEnd_2239150 < baseStart_2239150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239152 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_2239152 : Nat := 118140960795 + 2239152 * 2 ^ 59
def prefixEnd_2239152 : Nat := 4983230072969 + 3 ^ 40 * 2239152 * 2
def baseEnd_2239152 : Nat := 1149761234476328541202333

theorem tailTrace_2239152 : CollatzResearch.WordTrace tailWord_2239152 prefixEnd_2239152 1149761234476328541202333 := by
  unfold tailWord_2239152
  simp only [CollatzResearch.WordTrace]
  refine ⟨40834291391971097780479855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54445721855961463707306473 40834291391971097780479855)
  ·
    refine ⟨61251437087956646670719783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40834291391971097780479855 61251437087956646670719783)
    ·
      refine ⟨91877155631934970006079675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61251437087956646670719783 91877155631934970006079675)
      ·
        refine ⟨137815733447902455009119513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91877155631934970006079675 137815733447902455009119513)
        ·
          refine ⟨103361800085926841256839635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137815733447902455009119513 103361800085926841256839635)
          ·
            refine ⟨155042700128890261885259453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103361800085926841256839635 155042700128890261885259453)
            ·
              refine ⟨58141012548333848206972295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155042700128890261885259453 58141012548333848206972295)
              ·
                refine ⟨87211518822500772310458443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58141012548333848206972295 87211518822500772310458443)
                ·
                  refine ⟨130817278233751158465687665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87211518822500772310458443 130817278233751158465687665)
                  ·
                    refine ⟨98112958675313368849265749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130817278233751158465687665 98112958675313368849265749)
                    ·
                      refine ⟨1149761234476328541202333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 98112958675313368849265749 1149761234476328541202333)
                      ·
                        rfl

theorem cell23_2239152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_2239152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239152 prefixEnd_2239152 := by exact prefixLift 2239152
  have htrace : WordTrace (prefixWord ++ tailWord_2239152) baseStart_2239152 baseEnd_2239152 := by
    simpa [prefixWord, tailWord_2239152, baseEnd_2239152] using wordTrace_append hprefix tailTrace_2239152
  have hstable : (prefixWord ++ tailWord_2239152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239152).length < 2 ^ (prefixWord ++ tailWord_2239152).sum := by decide
  have hdescent : baseEnd_2239152 < baseStart_2239152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239180 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2239180 : Nat := 118140960795 + 2239180 * 2 ^ 59
def prefixEnd_2239180 : Nat := 4983230072969 + 3 ^ 40 * 2239180 * 2
def baseEnd_2239180 : Nat := 1149775611934654431652205

theorem tailTrace_2239180 : CollatzResearch.WordTrace tailWord_2239180 prefixEnd_2239180 1149775611934654431652205 := by
  unfold tailWord_2239180
  simp only [CollatzResearch.WordTrace]
  refine ⟨40834802013920378171489497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54446402685227170895319329 40834802013920378171489497)
  ·
    refine ⟨30626101510440283628617123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40834802013920378171489497 30626101510440283628617123)
    ·
      refine ⟨45939152265660425442925685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30626101510440283628617123 45939152265660425442925685)
      ·
        refine ⟨4306795524905664885274283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45939152265660425442925685 4306795524905664885274283)
        ·
          refine ⟨6460193287358497327911425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306795524905664885274283 6460193287358497327911425)
          ·
            refine ⟨4845144965518872995933569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460193287358497327911425 4845144965518872995933569)
            ·
              refine ⟨3633858724139154746950177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845144965518872995933569 3633858724139154746950177)
              ·
                refine ⟨2725394043104366060212633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633858724139154746950177 2725394043104366060212633)
                ·
                  refine ⟨2044045532328274545159475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725394043104366060212633 2044045532328274545159475)
                  ·
                    refine ⟨3066068298492411817739213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044045532328274545159475 3066068298492411817739213)
                    ·
                      refine ⟨1149775611934654431652205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066068298492411817739213 1149775611934654431652205)
                      ·
                        rfl

theorem cell23_2239180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2239180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239180 prefixEnd_2239180 := by exact prefixLift 2239180
  have htrace : WordTrace (prefixWord ++ tailWord_2239180) baseStart_2239180 baseEnd_2239180 := by
    simpa [prefixWord, tailWord_2239180, baseEnd_2239180] using wordTrace_append hprefix tailTrace_2239180
  have hstable : (prefixWord ++ tailWord_2239180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239180).length < 2 ^ (prefixWord ++ tailWord_2239180).sum := by decide
  have hdescent : baseEnd_2239180 < baseStart_2239180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239196 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2239196 : Nat := 118140960795 + 2239196 * 2 ^ 59
def prefixEnd_2239196 : Nat := 4983230072969 + 3 ^ 40 * 2239196 * 2
def baseEnd_2239196 : Nat := 383261275875042123017377

theorem tailTrace_2239196 : CollatzResearch.WordTrace tailWord_2239196 prefixEnd_2239196 383261275875042123017377 := by
  unfold tailWord_2239196
  simp only [CollatzResearch.WordTrace]
  refine ⟨40835093797891395537780721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54446791730521860717040961 40835093797891395537780721)
  ·
    refine ⟨30626320348418546653335541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40835093797891395537780721 30626320348418546653335541)
    ·
      refine ⟨2871217532664238748750207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30626320348418546653335541 2871217532664238748750207)
      ·
        refine ⟨4306826298996358123125311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871217532664238748750207 4306826298996358123125311)
        ·
          refine ⟨6460239448494537184687967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306826298996358123125311 6460239448494537184687967)
          ·
            refine ⟨9690359172741805777031951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460239448494537184687967 9690359172741805777031951)
            ·
              refine ⟨14535538759112708665547927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9690359172741805777031951 14535538759112708665547927)
              ·
                refine ⟨21803308138669062998321891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14535538759112708665547927 21803308138669062998321891)
                ·
                  refine ⟨32704962208003594497482837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21803308138669062998321891 32704962208003594497482837)
                  ·
                    refine ⟨383261275875042123017377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32704962208003594497482837 383261275875042123017377)
                    ·
                      rfl

theorem cell23_2239196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2239196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239196 prefixEnd_2239196 := by exact prefixLift 2239196
  have htrace : WordTrace (prefixWord ++ tailWord_2239196) baseStart_2239196 baseEnd_2239196 := by
    simpa [prefixWord, tailWord_2239196, baseEnd_2239196] using wordTrace_append hprefix tailTrace_2239196
  have hstable : (prefixWord ++ tailWord_2239196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239196).length < 2 ^ (prefixWord ++ tailWord_2239196).sum := by decide
  have hdescent : baseEnd_2239196 < baseStart_2239196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239199 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_2239199 : Nat := 118140960795 + 2239199 * 2 ^ 59
def prefixEnd_2239199 : Nat := 4983230072969 + 3 ^ 40 * 2239199 * 2
def baseEnd_2239199 : Nat := 1149785368067089857314617

theorem tailTrace_2239199 : CollatzResearch.WordTrace tailWord_2239199 prefixEnd_2239199 1149785368067089857314617 := by
  unfold tailWord_2239199
  simp only [CollatzResearch.WordTrace]
  refine ⟨81670297014771922587920651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54446864676514615058613767 81670297014771922587920651)
  ·
    refine ⟨122505445522157883881880977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81670297014771922587920651 122505445522157883881880977)
    ·
      refine ⟨91879084141618412911410733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122505445522157883881880977 91879084141618412911410733)
      ·
        refine ⟨34454656553106904841779025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91879084141618412911410733 34454656553106904841779025)
        ·
          refine ⟨25840992414830178631334269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34454656553106904841779025 25840992414830178631334269)
          ·
            refine ⟨9690372155561316986750351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25840992414830178631334269 9690372155561316986750351)
            ·
              refine ⟨14535558233341975480125527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9690372155561316986750351 14535558233341975480125527)
              ·
                refine ⟨21803337350012963220188291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14535558233341975480125527 21803337350012963220188291)
                ·
                  refine ⟨32705006025019444830282437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21803337350012963220188291 32705006025019444830282437)
                  ·
                    refine ⟨6132188629691145905677957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32705006025019444830282437 6132188629691145905677957)
                    ·
                      refine ⟨1149785368067089857314617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6132188629691145905677957 1149785368067089857314617)
                      ·
                        rfl

theorem cell23_2239199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_2239199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239199 prefixEnd_2239199 := by exact prefixLift 2239199
  have htrace : WordTrace (prefixWord ++ tailWord_2239199) baseStart_2239199 baseEnd_2239199 := by
    simpa [prefixWord, tailWord_2239199, baseEnd_2239199] using wordTrace_append hprefix tailTrace_2239199
  have hstable : (prefixWord ++ tailWord_2239199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239199).length < 2 ^ (prefixWord ++ tailWord_2239199).sum := by decide
  have hdescent : baseEnd_2239199 < baseStart_2239199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239203 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2239203 : Nat := 118140960795 + 2239203 * 2 ^ 59
def prefixEnd_2239203 : Nat := 4983230072969 + 3 ^ 40 * 2239203 * 2
def baseEnd_2239203 : Nat := 1149787421989707841664599

theorem tailTrace_2239203 : CollatzResearch.WordTrace tailWord_2239203 prefixEnd_2239203 1149787421989707841664599 := by
  unfold tailWord_2239203
  simp only [CollatzResearch.WordTrace]
  refine ⟨81670442906757431271066263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54446961937838287514044175 81670442906757431271066263)
  ·
    refine ⟨122505664360136146906599395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81670442906757431271066263 122505664360136146906599395)
    ·
      refine ⟨183758496540204220359899093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122505664360136146906599395 183758496540204220359899093)
      ·
        refine ⟨4306839762661036414685135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 183758496540204220359899093 4306839762661036414685135)
        ·
          refine ⟨6460259643991554622027703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306839762661036414685135 6460259643991554622027703)
          ·
            refine ⟨9690389465987331933041555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460259643991554622027703 9690389465987331933041555)
            ·
              refine ⟨14535584198980997899562333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9690389465987331933041555 14535584198980997899562333)
              ·
                refine ⟨5450844074617874212335875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14535584198980997899562333 5450844074617874212335875)
                ·
                  refine ⟨8176266111926811318503813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5450844074617874212335875 8176266111926811318503813)
                  ·
                    refine ⟨1533049895986277122219465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8176266111926811318503813 1533049895986277122219465)
                    ·
                      refine ⟨1149787421989707841664599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533049895986277122219465 1149787421989707841664599)
                      ·
                        rfl

theorem cell23_2239203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2239203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239203 prefixEnd_2239203 := by exact prefixLift 2239203
  have htrace : WordTrace (prefixWord ++ tailWord_2239203) baseStart_2239203 baseEnd_2239203 := by
    simpa [prefixWord, tailWord_2239203, baseEnd_2239203] using wordTrace_append hprefix tailTrace_2239203
  have hstable : (prefixWord ++ tailWord_2239203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239203).length < 2 ^ (prefixWord ++ tailWord_2239203).sum := by decide
  have hdescent : baseEnd_2239203 < baseStart_2239203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239219 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 3]
def baseStart_2239219 : Nat := 118140960795 + 2239219 * 2 ^ 59
def prefixEnd_2239219 : Nat := 4983230072969 + 3 ^ 40 * 2239219 * 2
def baseEnd_2239219 : Nat := 1149795637680179779064525

theorem tailTrace_2239219 : CollatzResearch.WordTrace tailWord_2239219 prefixEnd_2239219 1149795637680179779064525 := by
  unfold tailWord_2239219
  simp only [CollatzResearch.WordTrace]
  refine ⟨81671026474699466003648711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54447350983132977335765807 81671026474699466003648711)
  ·
    refine ⟨122506539712049199005473067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81671026474699466003648711 122506539712049199005473067)
    ·
      refine ⟨183759809568073798508209601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122506539712049199005473067 183759809568073798508209601)
      ·
        refine ⟨137819857176055348881157201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183759809568073798508209601 137819857176055348881157201)
        ·
          refine ⟨103364892882041511660867901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137819857176055348881157201 103364892882041511660867901)
          ·
            refine ⟨38761834830765566872825463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103364892882041511660867901 38761834830765566872825463)
            ·
              refine ⟨58142752246148350309238195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38761834830765566872825463 58142752246148350309238195)
              ·
                refine ⟨87214128369222525463857293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58142752246148350309238195 87214128369222525463857293)
                ·
                  refine ⟨32705298138458447048946485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87214128369222525463857293 32705298138458447048946485)
                  ·
                    refine ⟨3066121700480479410838733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32705298138458447048946485 3066121700480479410838733)
                    ·
                      refine ⟨1149795637680179779064525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066121700480479410838733 1149795637680179779064525)
                      ·
                        rfl

theorem cell23_2239219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_2239219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239219 prefixEnd_2239219 := by exact prefixLift 2239219
  have htrace : WordTrace (prefixWord ++ tailWord_2239219) baseStart_2239219 baseEnd_2239219 := by
    simpa [prefixWord, tailWord_2239219, baseEnd_2239219] using wordTrace_append hprefix tailTrace_2239219
  have hstable : (prefixWord ++ tailWord_2239219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239219).length < 2 ^ (prefixWord ++ tailWord_2239219).sum := by decide
  have hdescent : baseEnd_2239219 < baseStart_2239219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239226 : List Nat := [3, 1, 1, 1, 1, 3, 3, 5, 5]
def baseStart_2239226 : Nat := 118140960795 + 2239226 * 2 ^ 59
def prefixEnd_2239226 : Nat := 4983230072969 + 3 ^ 40 * 2239226 * 2
def baseEnd_2239226 : Nat := 127755470227195694630777

theorem tailTrace_2239226 : CollatzResearch.WordTrace tailWord_2239226 prefixEnd_2239226 127755470227195694630777 := by
  unfold tailWord_2239226
  simp only [CollatzResearch.WordTrace]
  refine ⟨20417820446418526549788383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54447521190449404132769021 20417820446418526549788383)
  ·
    refine ⟨30626730669627789824682575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20417820446418526549788383 30626730669627789824682575)
    ·
      refine ⟨45940096004441684737023863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30626730669627789824682575 45940096004441684737023863)
      ·
        refine ⟨68910144006662527105535795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45940096004441684737023863 68910144006662527105535795)
        ·
          refine ⟨103365216009993790658303693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68910144006662527105535795 103365216009993790658303693)
          ·
            refine ⟨38761956003747671496863885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103365216009993790658303693 38761956003747671496863885)
            ·
              refine ⟨14535733501405376811323957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38761956003747671496863885 14535733501405376811323957)
              ·
                refine ⟨1362725015756754076061621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14535733501405376811323957 1362725015756754076061621)
                ·
                  refine ⟨127755470227195694630777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1362725015756754076061621 127755470227195694630777)
                  ·
                    rfl

theorem cell23_2239226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_2239226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239226 prefixEnd_2239226 := by exact prefixLift 2239226
  have htrace : WordTrace (prefixWord ++ tailWord_2239226) baseStart_2239226 baseEnd_2239226 := by
    simpa [prefixWord, tailWord_2239226, baseEnd_2239226] using wordTrace_append hprefix tailTrace_2239226
  have hstable : (prefixWord ++ tailWord_2239226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239226).length < 2 ^ (prefixWord ++ tailWord_2239226).sum := by decide
  have hdescent : baseEnd_2239226 < baseStart_2239226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239236 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2239236 : Nat := 118140960795 + 2239236 * 2 ^ 59
def prefixEnd_2239236 : Nat := 4983230072969 + 3 ^ 40 * 2239236 * 2
def baseEnd_2239236 : Nat := 1149804366851306212551947

theorem tailTrace_2239236 : CollatzResearch.WordTrace tailWord_2239236 prefixEnd_2239236 1149804366851306212551947 := by
  unfold tailWord_2239236
  simp only [CollatzResearch.WordTrace]
  refine ⟨40835823257818938953508781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54447764343758585271345041 40835823257818938953508781)
  ·
    refine ⟨15313433721682102107565793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40835823257818938953508781 15313433721682102107565793)
    ·
      refine ⟨11485075291261576580674345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15313433721682102107565793 11485075291261576580674345)
      ·
        refine ⟨8613806468446182435505759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11485075291261576580674345 8613806468446182435505759)
        ·
          refine ⟨12920709702669273653258639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8613806468446182435505759 12920709702669273653258639)
          ·
            refine ⟨19381064554003910479887959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12920709702669273653258639 19381064554003910479887959)
            ·
              refine ⟨29071596831005865719831939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19381064554003910479887959 29071596831005865719831939)
              ·
                refine ⟨43607395246508798579747909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29071596831005865719831939 43607395246508798579747909)
                ·
                  refine ⟨8176386608720399733702733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43607395246508798579747909 8176386608720399733702733)
                  ·
                    refine ⟨3066144978270149900138525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8176386608720399733702733 3066144978270149900138525)
                    ·
                      refine ⟨1149804366851306212551947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066144978270149900138525 1149804366851306212551947)
                      ·
                        rfl

theorem cell23_2239236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2239236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239236 prefixEnd_2239236 := by exact prefixLift 2239236
  have htrace : WordTrace (prefixWord ++ tailWord_2239236) baseStart_2239236 baseEnd_2239236 := by
    simpa [prefixWord, tailWord_2239236, baseEnd_2239236] using wordTrace_append hprefix tailTrace_2239236
  have hstable : (prefixWord ++ tailWord_2239236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239236).length < 2 ^ (prefixWord ++ tailWord_2239236).sum := by decide
  have hdescent : baseEnd_2239236 < baseStart_2239236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239249 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_2239249 : Nat := 118140960795 + 2239249 * 2 ^ 59
def prefixEnd_2239249 : Nat := 4983230072969 + 3 ^ 40 * 2239249 * 2
def baseEnd_2239249 : Nat := 1149811042099814661689387

theorem tailTrace_2239249 : CollatzResearch.WordTrace tailWord_2239249 prefixEnd_2239249 1149811042099814661689387 := by
  unfold tailWord_2239249
  simp only [CollatzResearch.WordTrace]
  refine ⟨81672120664590781127240801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54448080443060520751493867 81672120664590781127240801)
  ·
    refine ⟨61254090498443085845430601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81672120664590781127240801 61254090498443085845430601)
    ·
      refine ⟨45940567873832314384072951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61254090498443085845430601 45940567873832314384072951)
      ·
        refine ⟨68910851810748471576109427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45940567873832314384072951 68910851810748471576109427)
        ·
          refine ⟨103366277716122707364164141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68910851810748471576109427 103366277716122707364164141)
          ·
            refine ⟨38762354143546015261561553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103366277716122707364164141 38762354143546015261561553)
            ·
              refine ⟨29071765607659511446171165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38762354143546015261561553 29071765607659511446171165)
              ·
                refine ⟨10901912102872316792314187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29071765607659511446171165 10901912102872316792314187)
                ·
                  refine ⟨16352868154308475188471281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10901912102872316792314187 16352868154308475188471281)
                  ·
                    refine ⟨12264651115731356391353461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16352868154308475188471281 12264651115731356391353461)
                    ·
                      refine ⟨1149811042099814661689387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12264651115731356391353461 1149811042099814661689387)
                      ·
                        rfl

theorem cell23_2239249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_2239249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239249 prefixEnd_2239249 := by exact prefixLift 2239249
  have htrace : WordTrace (prefixWord ++ tailWord_2239249) baseStart_2239249 baseEnd_2239249 := by
    simpa [prefixWord, tailWord_2239249, baseEnd_2239249] using wordTrace_append hprefix tailTrace_2239249
  have hstable : (prefixWord ++ tailWord_2239249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239249).length < 2 ^ (prefixWord ++ tailWord_2239249).sum := by decide
  have hdescent : baseEnd_2239249 < baseStart_2239249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239269 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_2239269 : Nat := 118140960795 + 2239269 * 2 ^ 59
def prefixEnd_2239269 : Nat := 4983230072969 + 3 ^ 40 * 2239269 * 2
def baseEnd_2239269 : Nat := 383273770570968194479765

theorem tailTrace_2239269 : CollatzResearch.WordTrace tailWord_2239269 prefixEnd_2239269 383273770570968194479765 := by
  unfold tailWord_2239269
  simp only [CollatzResearch.WordTrace]
  refine ⟨81672850124518324542968861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54448566749678883028645907 81672850124518324542968861)
  ·
    refine ⟨30627318796694371703613323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81672850124518324542968861 30627318796694371703613323)
    ·
      refine ⟨45940978195041557555419985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30627318796694371703613323 45940978195041557555419985)
      ·
        refine ⟨34455733646281168166564989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45940978195041557555419985 34455733646281168166564989)
        ·
          refine ⟨12920900117355438062461871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34455733646281168166564989 12920900117355438062461871)
          ·
            refine ⟨19381350176033157093692807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12920900117355438062461871 19381350176033157093692807)
            ·
              refine ⟨29072025264049735640539211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19381350176033157093692807 29072025264049735640539211)
              ·
                refine ⟨43608037896074603460808817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29072025264049735640539211 43608037896074603460808817)
                ·
                  refine ⟨32706028422055952595606613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43608037896074603460808817 32706028422055952595606613)
                  ·
                    refine ⟨383273770570968194479765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32706028422055952595606613 383273770570968194479765)
                    ·
                      rfl

theorem cell23_2239269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_2239269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239269 prefixEnd_2239269 := by exact prefixLift 2239269
  have htrace : WordTrace (prefixWord ++ tailWord_2239269) baseStart_2239269 baseEnd_2239269 := by
    simpa [prefixWord, tailWord_2239269, baseEnd_2239269] using wordTrace_append hprefix tailTrace_2239269
  have hstable : (prefixWord ++ tailWord_2239269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239269).length < 2 ^ (prefixWord ++ tailWord_2239269).sum := by decide
  have hdescent : baseEnd_2239269 < baseStart_2239269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239276 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_2239276 : Nat := 118140960795 + 2239276 * 2 ^ 59
def prefixEnd_2239276 : Nat := 4983230072969 + 3 ^ 40 * 2239276 * 2
def baseEnd_2239276 : Nat := 1149824906077486056051763

theorem tailTrace_2239276 : CollatzResearch.WordTrace tailWord_2239276 prefixEnd_2239276 1149824906077486056051763 := by
  unfold tailWord_2239276
  simp only [CollatzResearch.WordTrace]
  refine ⟨40836552717746482369236841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54448736956995309825649121 40836552717746482369236841)
  ·
    refine ⟨30627414538309861776927631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40836552717746482369236841 30627414538309861776927631)
    ·
      refine ⟨45941121807464792665391447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30627414538309861776927631 45941121807464792665391447)
      ·
        refine ⟨68911682711197188998087171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45941121807464792665391447 68911682711197188998087171)
        ·
          refine ⟨103367524066795783497130757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68911682711197188998087171 103367524066795783497130757)
          ·
            refine ⟨19381410762524209405712017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103367524066795783497130757 19381410762524209405712017)
            ·
              refine ⟨14536058071893157054284013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19381410762524209405712017 14536058071893157054284013)
              ·
                refine ⟨5451021776959933895356505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14536058071893157054284013 5451021776959933895356505)
                ·
                  refine ⟨4088266332719950421517379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5451021776959933895356505 4088266332719950421517379)
                  ·
                    refine ⟨6132399499079925632276069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4088266332719950421517379 6132399499079925632276069)
                    ·
                      refine ⟨1149824906077486056051763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6132399499079925632276069 1149824906077486056051763)
                      ·
                        rfl

theorem cell23_2239276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_2239276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239276 prefixEnd_2239276 := by exact prefixLift 2239276
  have htrace : WordTrace (prefixWord ++ tailWord_2239276) baseStart_2239276 baseEnd_2239276 := by
    simpa [prefixWord, tailWord_2239276, baseEnd_2239276] using wordTrace_append hprefix tailTrace_2239276
  have hstable : (prefixWord ++ tailWord_2239276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239276).length < 2 ^ (prefixWord ++ tailWord_2239276).sum := by decide
  have hdescent : baseEnd_2239276 < baseStart_2239276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239299 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 8]
def baseStart_2239299 : Nat := 118140960795 + 2239299 * 2 ^ 59
def prefixEnd_2239299 : Nat := 4983230072969 + 3 ^ 40 * 2239299 * 2
def baseEnd_2239299 : Nat := 127759635125837718451573

theorem tailTrace_2239299 : CollatzResearch.WordTrace tailWord_2239299 prefixEnd_2239299 127759635125837718451573 := by
  unfold tailWord_2239299
  simp only [CollatzResearch.WordTrace]
  refine ⟨81673944314409639666560951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54449296209606426444373967 81673944314409639666560951)
  ·
    refine ⟨122510916471614459499841427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81673944314409639666560951 122510916471614459499841427)
    ·
      refine ⟨183766374707421689249762141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122510916471614459499841427 183766374707421689249762141)
      ·
        refine ⟨68912390515283133468660803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183766374707421689249762141 68912390515283133468660803)
        ·
          refine ⟨103368585772924700202991205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68912390515283133468660803 103368585772924700202991205)
          ·
            refine ⟨19381609832423381288060851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103368585772924700202991205 19381609832423381288060851)
            ·
              refine ⟨29072414748635071932091277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19381609832423381288060851 29072414748635071932091277)
              ·
                refine ⟨10902155530738151974534229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29072414748635071932091277 10902155530738151974534229)
                ·
                  refine ⟨127759635125837718451573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10902155530738151974534229 127759635125837718451573)
                  ·
                    rfl

theorem cell23_2239299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 8].length) (baseStart_2239299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239299 prefixEnd_2239299 := by exact prefixLift 2239299
  have htrace : WordTrace (prefixWord ++ tailWord_2239299) baseStart_2239299 baseEnd_2239299 := by
    simpa [prefixWord, tailWord_2239299, baseEnd_2239299] using wordTrace_append hprefix tailTrace_2239299
  have hstable : (prefixWord ++ tailWord_2239299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239299).length < 2 ^ (prefixWord ++ tailWord_2239299).sum := by decide
  have hdescent : baseEnd_2239299 < baseStart_2239299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239300 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2239300 : Nat := 118140960795 + 2239300 * 2 ^ 59
def prefixEnd_2239300 : Nat := 4983230072969 + 3 ^ 40 * 2239300 * 2
def baseEnd_2239300 : Nat := 1149837229613193962151653

theorem tailTrace_2239300 : CollatzResearch.WordTrace tailWord_2239300 prefixEnd_2239300 1149837229613193962151653 := by
  unfold tailWord_2239300
  simp only [CollatzResearch.WordTrace]
  refine ⟨40836990393703008418673677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54449320524937344558231569 40836990393703008418673677)
  ·
    refine ⟨15313871397638628157002629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40836990393703008418673677 15313871397638628157002629)
    ·
      refine ⟨2871350887057242779437993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15313871397638628157002629 2871350887057242779437993)
      ·
        refine ⟨2153513165292932084578495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2871350887057242779437993 2153513165292932084578495)
        ·
          refine ⟨3230269747939398126867743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2153513165292932084578495 3230269747939398126867743)
          ·
            refine ⟨4845404621909097190301615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230269747939398126867743 4845404621909097190301615)
            ·
              refine ⟨7268106932863645785452423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4845404621909097190301615 7268106932863645785452423)
              ·
                refine ⟨10902160399295468678178635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7268106932863645785452423 10902160399295468678178635)
                ·
                  refine ⟨16353240598943203017267953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10902160399295468678178635 16353240598943203017267953)
                  ·
                    refine ⟨12264930449207402262950965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16353240598943203017267953 12264930449207402262950965)
                    ·
                      refine ⟨1149837229613193962151653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12264930449207402262950965 1149837229613193962151653)
                      ·
                        rfl

theorem cell23_2239300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2239300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239300 prefixEnd_2239300 := by exact prefixLift 2239300
  have htrace : WordTrace (prefixWord ++ tailWord_2239300) baseStart_2239300 baseEnd_2239300 := by
    simpa [prefixWord, tailWord_2239300, baseEnd_2239300] using wordTrace_append hprefix tailTrace_2239300
  have hstable : (prefixWord ++ tailWord_2239300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239300).length < 2 ^ (prefixWord ++ tailWord_2239300).sum := by decide
  have hdescent : baseEnd_2239300 < baseStart_2239300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239350 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_2239350 : Nat := 118140960795 + 2239350 * 2 ^ 59
def prefixEnd_2239350 : Nat := 4983230072969 + 3 ^ 40 * 2239350 * 2
def baseEnd_2239350 : Nat := 127762544849546529614047

theorem tailTrace_2239350 : CollatzResearch.WordTrace tailWord_2239350 prefixEnd_2239350 127762544849546529614047 := by
  unfold tailWord_2239350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5104737777326554711041719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54450536291483250251111669 5104737777326554711041719)
  ·
    refine ⟨7657106665989832066562579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5104737777326554711041719 7657106665989832066562579)
    ·
      refine ⟨11485659998984748099843869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7657106665989832066562579 11485659998984748099843869)
      ·
        refine ⟨4307122499619280537441451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11485659998984748099843869 4307122499619280537441451)
        ·
          refine ⟨6460683749428920806162177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307122499619280537441451 6460683749428920806162177)
          ·
            refine ⟨4845512812071690604621633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460683749428920806162177 4845512812071690604621633)
            ·
              refine ⟨3634134609053767953466225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845512812071690604621633 3634134609053767953466225)
              ·
                refine ⟨2725600956790325965099669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3634134609053767953466225 2725600956790325965099669)
                ·
                  refine ⟨127762544849546529614047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2725600956790325965099669 127762544849546529614047)
                  ·
                    rfl

theorem cell23_2239350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_2239350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239350 prefixEnd_2239350 := by exact prefixLift 2239350
  have htrace : WordTrace (prefixWord ++ tailWord_2239350) baseStart_2239350 baseEnd_2239350 := by
    simpa [prefixWord, tailWord_2239350, baseEnd_2239350] using wordTrace_append hprefix tailTrace_2239350
  have hstable : (prefixWord ++ tailWord_2239350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239350).length < 2 ^ (prefixWord ++ tailWord_2239350).sum := by decide
  have hdescent : baseEnd_2239350 < baseStart_2239350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239383 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_2239383 : Nat := 118140960795 + 2239383 * 2 ^ 59
def prefixEnd_2239383 : Nat := 4983230072969 + 3 ^ 40 * 2239383 * 2
def baseEnd_2239383 : Nat := 1149879848507517137413771

theorem tailTrace_2239383 : CollatzResearch.WordTrace tailWord_2239383 prefixEnd_2239383 1149879848507517137413771 := by
  unfold tailWord_2239383
  simp only [CollatzResearch.WordTrace]
  refine ⟨81677008046105322012618803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54451338697403548008412535 81677008046105322012618803)
  ·
    refine ⟨122515512069157983018928205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81677008046105322012618803 122515512069157983018928205)
    ·
      refine ⟨45943317025934243632098077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122515512069157983018928205 45943317025934243632098077)
      ·
        refine ⟨17228743884725341362036779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45943317025934243632098077 17228743884725341362036779)
        ·
          refine ⟨25843115827088012043055169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17228743884725341362036779 25843115827088012043055169)
          ·
            refine ⟨19382336870316009032291377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25843115827088012043055169 19382336870316009032291377)
            ·
              refine ⟨14536752652737006774218533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19382336870316009032291377 14536752652737006774218533)
              ·
                refine ⟨2725641122388188770165975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14536752652737006774218533 2725641122388188770165975)
                ·
                  refine ⟨4088461683582283155248963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725641122388188770165975 4088461683582283155248963)
                  ·
                    refine ⟨6132692525373424732873445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4088461683582283155248963 6132692525373424732873445)
                    ·
                      refine ⟨1149879848507517137413771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6132692525373424732873445 1149879848507517137413771)
                      ·
                        rfl

theorem cell23_2239383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_2239383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239383 prefixEnd_2239383 := by exact prefixLift 2239383
  have htrace : WordTrace (prefixWord ++ tailWord_2239383) baseStart_2239383 baseEnd_2239383 := by
    simpa [prefixWord, tailWord_2239383, baseEnd_2239383] using wordTrace_append hprefix tailTrace_2239383
  have hstable : (prefixWord ++ tailWord_2239383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239383).length < 2 ^ (prefixWord ++ tailWord_2239383).sum := by decide
  have hdescent : baseEnd_2239383 < baseStart_2239383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239393 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 1, 6]
def baseStart_2239393 : Nat := 118140960795 + 2239393 * 2 ^ 59
def prefixEnd_2239393 : Nat := 4983230072969 + 3 ^ 40 * 2239393 * 2
def baseEnd_2239393 : Nat := 383294994438020699429575

theorem tailTrace_2239393 : CollatzResearch.WordTrace tailWord_2239393 prefixEnd_2239393 383294994438020699429575 := by
  unfold tailWord_2239393
  simp only [CollatzResearch.WordTrace]
  refine ⟨81677372776069093720482833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54451581850712729146988555 81677372776069093720482833)
  ·
    refine ⟨61258029582051820290362125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81677372776069093720482833 61258029582051820290362125)
    ·
      refine ⟨22971761093269432608885797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61258029582051820290362125 22971761093269432608885797)
      ·
        refine ⟨4307205204988018614166087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22971761093269432608885797 4307205204988018614166087)
        ·
          refine ⟨6460807807482027921249131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307205204988018614166087 6460807807482027921249131)
          ·
            refine ⟨9691211711223041881873697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460807807482027921249131 9691211711223041881873697)
            ·
              refine ⟨7268408783417281411405273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9691211711223041881873697 7268408783417281411405273)
              ·
                refine ⟨5451306587562961058553955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7268408783417281411405273 5451306587562961058553955)
                ·
                  refine ⟨8176959881344441587830933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5451306587562961058553955 8176959881344441587830933)
                  ·
                    refine ⟨383294994438020699429575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8176959881344441587830933 383294994438020699429575)
                    ·
                      rfl

theorem cell23_2239393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_2239393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239393 prefixEnd_2239393 := by exact prefixLift 2239393
  have htrace : WordTrace (prefixWord ++ tailWord_2239393) baseStart_2239393 baseEnd_2239393 := by
    simpa [prefixWord, tailWord_2239393, baseEnd_2239393] using wordTrace_append hprefix tailTrace_2239393
  have hstable : (prefixWord ++ tailWord_2239393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239393).length < 2 ^ (prefixWord ++ tailWord_2239393).sum := by decide
  have hdescent : baseEnd_2239393 < baseStart_2239393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239394 : List Nat := [3, 3, 1, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_2239394 : Nat := 118140960795 + 2239394 * 2 ^ 59
def prefixEnd_2239394 : Nat := 4983230072969 + 3 ^ 40 * 2239394 * 2
def baseEnd_2239394 : Nat := 1149885496794716594376221

theorem tailTrace_2239394 : CollatzResearch.WordTrace tailWord_2239394 prefixEnd_2239394 1149885496794716594376221 := by
  unfold tailWord_2239394
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419352312266367722817309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54451606166043647260846157 20419352312266367722817309)
  ·
    refine ⟨7657257117099887896056491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20419352312266367722817309 7657257117099887896056491)
    ·
      refine ⟨11485885675649831844084737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7657257117099887896056491 11485885675649831844084737)
      ·
        refine ⟨8614414256737373883063553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11485885675649831844084737 8614414256737373883063553)
        ·
          refine ⟨6460810692553030412297665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8614414256737373883063553 6460810692553030412297665)
          ·
            refine ⟨4845608019414772809223249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460810692553030412297665 4845608019414772809223249)
            ·
              refine ⟨3634206014561079606917437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845608019414772809223249 3634206014561079606917437)
              ·
                refine ⟨1362827255460404852594039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634206014561079606917437 1362827255460404852594039)
                ·
                  refine ⟨2044240883190607278891059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362827255460404852594039 2044240883190607278891059)
                  ·
                    refine ⟨3066361324785910918336589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044240883190607278891059 3066361324785910918336589)
                    ·
                      refine ⟨1149885496794716594376221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066361324785910918336589 1149885496794716594376221)
                      ·
                        rfl

theorem cell23_2239394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_2239394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239394 prefixEnd_2239394 := by exact prefixLift 2239394
  have htrace : WordTrace (prefixWord ++ tailWord_2239394) baseStart_2239394 baseEnd_2239394 := by
    simpa [prefixWord, tailWord_2239394, baseEnd_2239394] using wordTrace_append hprefix tailTrace_2239394
  have hstable : (prefixWord ++ tailWord_2239394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239394).length < 2 ^ (prefixWord ++ tailWord_2239394).sum := by decide
  have hdescent : baseEnd_2239394 < baseStart_2239394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239403 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 3]
def baseStart_2239403 : Nat := 118140960795 + 2239403 * 2 ^ 59
def prefixEnd_2239403 : Nat := 4983230072969 + 3 ^ 40 * 2239403 * 2
def baseEnd_2239403 : Nat := 1149890118120607059163679

theorem tailTrace_2239403 : CollatzResearch.WordTrace tailWord_2239403 prefixEnd_2239403 1149890118120607059163679 := by
  unfold tailWord_2239403
  simp only [CollatzResearch.WordTrace]
  refine ⟨81677737506032865428346863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54451825004021910285564575 81677737506032865428346863)
  ·
    refine ⟨122516606259049298142520295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81677737506032865428346863 122516606259049298142520295)
    ·
      refine ⟨183774909388573947213780443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122516606259049298142520295 183774909388573947213780443)
      ·
        refine ⟨275662364082860920820670665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183774909388573947213780443 275662364082860920820670665)
        ·
          refine ⟨206746773062145690615502999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275662364082860920820670665 206746773062145690615502999)
          ·
            refine ⟨310120159593218535923254499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206746773062145690615502999 310120159593218535923254499)
            ·
              refine ⟨465180239389827803884881749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310120159593218535923254499 465180239389827803884881749)
              ·
                refine ⟨2725665465174772288387979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 465180239389827803884881749 2725665465174772288387979)
                ·
                  refine ⟨4088498197762158432581969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725665465174772288387979 4088498197762158432581969)
                  ·
                    refine ⟨3066373648321618824436477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4088498197762158432581969 3066373648321618824436477)
                    ·
                      refine ⟨1149890118120607059163679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066373648321618824436477 1149890118120607059163679)
                      ·
                        rfl

theorem cell23_2239403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 3].length) (baseStart_2239403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239403 prefixEnd_2239403 := by exact prefixLift 2239403
  have htrace : WordTrace (prefixWord ++ tailWord_2239403) baseStart_2239403 baseEnd_2239403 := by
    simpa [prefixWord, tailWord_2239403, baseEnd_2239403] using wordTrace_append hprefix tailTrace_2239403
  have hstable : (prefixWord ++ tailWord_2239403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239403).length < 2 ^ (prefixWord ++ tailWord_2239403).sum := by decide
  have hdescent : baseEnd_2239403 < baseStart_2239403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239417 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 3, 2, 2]
def baseStart_2239417 : Nat := 118140960795 + 2239417 * 2 ^ 59
def prefixEnd_2239417 : Nat := 4983230072969 + 3 ^ 40 * 2239417 * 2
def baseEnd_2239417 : Nat := 1149897306849770004388615

theorem tailTrace_2239417 : CollatzResearch.WordTrace tailWord_2239417 prefixEnd_2239417 1149897306849770004388615 := by
  unfold tailWord_2239417
  simp only [CollatzResearch.WordTrace]
  refine ⟨81678248127982145819356505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54452165418654763879571003 81678248127982145819356505)
  ·
    refine ⟨61258686095986609364517379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81678248127982145819356505 61258686095986609364517379)
    ·
      refine ⟨91888029143979914046776069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61258686095986609364517379 91888029143979914046776069)
      ·
        refine ⟨17229005464496233883770513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91888029143979914046776069 17229005464496233883770513)
        ·
          refine ⟨12921754098372175412827885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17229005464496233883770513 12921754098372175412827885)
          ·
            refine ⟨4845657786889565779810457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12921754098372175412827885 4845657786889565779810457)
            ·
              refine ⟨3634243340167174334857843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845657786889565779810457 3634243340167174334857843)
              ·
                refine ⟨5451365010250761502286765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3634243340167174334857843 5451365010250761502286765)
                ·
                  refine ⟨2044261878844035563357537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5451365010250761502286765 2044261878844035563357537)
                  ·
                    refine ⟨1533196409133026672518153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2044261878844035563357537 1533196409133026672518153)
                    ·
                      refine ⟨1149897306849770004388615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533196409133026672518153 1149897306849770004388615)
                      ·
                        rfl

theorem cell23_2239417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_2239417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239417 prefixEnd_2239417 := by exact prefixLift 2239417
  have htrace : WordTrace (prefixWord ++ tailWord_2239417) baseStart_2239417 baseEnd_2239417 := by
    simpa [prefixWord, tailWord_2239417, baseEnd_2239417] using wordTrace_append hprefix tailTrace_2239417
  have hstable : (prefixWord ++ tailWord_2239417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239417).length < 2 ^ (prefixWord ++ tailWord_2239417).sum := by decide
  have hdescent : baseEnd_2239417 < baseStart_2239417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239433 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 3]
def baseStart_2239433 : Nat := 118140960795 + 2239433 * 2 ^ 59
def prefixEnd_2239433 : Nat := 4983230072969 + 3 ^ 40 * 2239433 * 2
def baseEnd_2239433 : Nat := 1149905522540241941788541

theorem tailTrace_2239433 : CollatzResearch.WordTrace tailWord_2239433 prefixEnd_2239433 1149905522540241941788541 := by
  unfold tailWord_2239433
  simp only [CollatzResearch.WordTrace]
  refine ⟨81678831695924180551938953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54452554463949453701292635 81678831695924180551938953)
  ·
    refine ⟨61259123771943135413954215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81678831695924180551938953 61259123771943135413954215)
    ·
      refine ⟨91888685657914703120931323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61259123771943135413954215 91888685657914703120931323)
      ·
        refine ⟨137833028486872054681396985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91888685657914703120931323 137833028486872054681396985)
        ·
          refine ⟨103374771365154041011047739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137833028486872054681396985 103374771365154041011047739)
          ·
            refine ⟨155062157047731061516571609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103374771365154041011047739 155062157047731061516571609)
            ·
              refine ⟨116296617785798296137428707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155062157047731061516571609 116296617785798296137428707)
              ·
                refine ⟨174444926678697444206143061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116296617785798296137428707 174444926678697444206143061)
                ·
                  refine ⟨2044276484515985674290739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 174444926678697444206143061 2044276484515985674290739)
                  ·
                    refine ⟨3066414726773978511436109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044276484515985674290739 3066414726773978511436109)
                    ·
                      refine ⟨1149905522540241941788541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066414726773978511436109 1149905522540241941788541)
                      ·
                        rfl

theorem cell23_2239433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 3].length) (baseStart_2239433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239433 prefixEnd_2239433 := by exact prefixLift 2239433
  have htrace : WordTrace (prefixWord ++ tailWord_2239433) baseStart_2239433 baseEnd_2239433 := by
    simpa [prefixWord, tailWord_2239433, baseEnd_2239433] using wordTrace_append hprefix tailTrace_2239433
  have hstable : (prefixWord ++ tailWord_2239433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239433).length < 2 ^ (prefixWord ++ tailWord_2239433).sum := by decide
  have hdescent : baseEnd_2239433 < baseStart_2239433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239450 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_2239450 : Nat := 118140960795 + 2239450 * 2 ^ 59
def prefixEnd_2239450 : Nat := 4983230072969 + 3 ^ 40 * 2239450 * 2
def baseEnd_2239450 : Nat := 1149914251711368375275963

theorem tailTrace_2239450 : CollatzResearch.WordTrace tailWord_2239450 prefixEnd_2239450 1149914251711368375275963 := by
  unfold tailWord_2239450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419862934215648113826951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54452967824575061636871869 20419862934215648113826951)
  ·
    refine ⟨30629794401323472170740427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20419862934215648113826951 30629794401323472170740427)
    ·
      refine ⟨45944691601985208256110641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30629794401323472170740427 45944691601985208256110641)
      ·
        refine ⟨34458518701488906192082981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45944691601985208256110641 34458518701488906192082981)
        ·
          refine ⟨6460972256529169911015559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34458518701488906192082981 6460972256529169911015559)
          ·
            refine ⟨9691458384793754866523339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460972256529169911015559 9691458384793754866523339)
            ·
              refine ⟨14537187577190632299785009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9691458384793754866523339 14537187577190632299785009)
              ·
                refine ⟨10902890682892974224838757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14537187577190632299785009 10902890682892974224838757)
                ·
                  refine ⟨2044292003042432667157267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10902890682892974224838757 2044292003042432667157267)
                  ·
                    refine ⟨3066438004563649000735901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044292003042432667157267 3066438004563649000735901)
                    ·
                      refine ⟨1149914251711368375275963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066438004563649000735901 1149914251711368375275963)
                      ·
                        rfl

theorem cell23_2239450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_2239450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239450 prefixEnd_2239450 := by exact prefixLift 2239450
  have htrace : WordTrace (prefixWord ++ tailWord_2239450) baseStart_2239450 baseEnd_2239450 := by
    simpa [prefixWord, tailWord_2239450, baseEnd_2239450] using wordTrace_append hprefix tailTrace_2239450
  have hstable : (prefixWord ++ tailWord_2239450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239450).length < 2 ^ (prefixWord ++ tailWord_2239450).sum := by decide
  have hdescent : baseEnd_2239450 < baseStart_2239450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239456 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2239456 : Nat := 118140960795 + 2239456 * 2 ^ 59
def prefixEnd_2239456 : Nat := 4983230072969 + 3 ^ 40 * 2239456 * 2
def baseEnd_2239456 : Nat := 1149917332595295351800935

theorem tailTrace_2239456 : CollatzResearch.WordTrace tailWord_2239456 prefixEnd_2239456 1149917332595295351800935 := by
  unfold tailWord_2239456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40839835287420427740013111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54453113716560570320017481 40839835287420427740013111)
  ·
    refine ⟨61259752931130641610019667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40839835287420427740013111 61259752931130641610019667)
    ·
      refine ⟨91889629396695962415029501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61259752931130641610019667 91889629396695962415029501)
      ·
        refine ⟨34458611023760985905636063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91889629396695962415029501 34458611023760985905636063)
        ·
          refine ⟨51687916535641478858454095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34458611023760985905636063 51687916535641478858454095)
          ·
            refine ⟨77531874803462218287681143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51687916535641478858454095 77531874803462218287681143)
            ·
              refine ⟨116297812205193327431521715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77531874803462218287681143 116297812205193327431521715)
              ·
                refine ⟨174446718307789991147282573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116297812205193327431521715 174446718307789991147282573)
                ·
                  refine ⟨65417519365421246680230965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174446718307789991147282573 65417519365421246680230965)
                  ·
                    refine ⟨6132892440508241876271653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65417519365421246680230965 6132892440508241876271653)
                    ·
                      refine ⟨1149917332595295351800935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6132892440508241876271653 1149917332595295351800935)
                      ·
                        rfl

theorem cell23_2239456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2239456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239456 prefixEnd_2239456 := by exact prefixLift 2239456
  have htrace : WordTrace (prefixWord ++ tailWord_2239456) baseStart_2239456 baseEnd_2239456 := by
    simpa [prefixWord, tailWord_2239456, baseEnd_2239456] using wordTrace_append hprefix tailTrace_2239456
  have hstable : (prefixWord ++ tailWord_2239456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239456).length < 2 ^ (prefixWord ++ tailWord_2239456).sum := by decide
  have hdescent : baseEnd_2239456 < baseStart_2239456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239484 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_2239484 : Nat := 118140960795 + 2239484 * 2 ^ 59
def prefixEnd_2239484 : Nat := 4983230072969 + 3 ^ 40 * 2239484 * 2
def baseEnd_2239484 : Nat := 1149931710053621242250807

theorem tailTrace_2239484 : CollatzResearch.WordTrace tailWord_2239484 prefixEnd_2239484 1149931710053621242250807 := by
  unfold tailWord_2239484
  simp only [CollatzResearch.WordTrace]
  refine ⟨40840345909369708131022753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54453794545826277508030337 40840345909369708131022753)
  ·
    refine ⟨30630259432027281098267065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40840345909369708131022753 30630259432027281098267065)
    ·
      refine ⟨22972694574020460823700299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30630259432027281098267065 22972694574020460823700299)
      ·
        refine ⟨34459041861030691235550449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22972694574020460823700299 34459041861030691235550449)
        ·
          refine ⟨25844281395773018426662837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34459041861030691235550449 25844281395773018426662837)
          ·
            refine ⟨2422901380853720477499641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25844281395773018426662837 2422901380853720477499641)
            ·
              refine ⟨1817176035640290358124731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422901380853720477499641 1817176035640290358124731)
              ·
                refine ⟨2725764053460435537187097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817176035640290358124731 2725764053460435537187097)
                ·
                  refine ⟨2044323040095326652890323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725764053460435537187097 2044323040095326652890323)
                  ·
                    refine ⟨3066484560142989979335485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044323040095326652890323 3066484560142989979335485)
                    ·
                      refine ⟨1149931710053621242250807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066484560142989979335485 1149931710053621242250807)
                      ·
                        rfl

theorem cell23_2239484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_2239484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239484 prefixEnd_2239484 := by exact prefixLift 2239484
  have htrace : WordTrace (prefixWord ++ tailWord_2239484) baseStart_2239484 baseEnd_2239484 := by
    simpa [prefixWord, tailWord_2239484, baseEnd_2239484] using wordTrace_append hprefix tailTrace_2239484
  have hstable : (prefixWord ++ tailWord_2239484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239484).length < 2 ^ (prefixWord ++ tailWord_2239484).sum := by decide
  have hdescent : baseEnd_2239484 < baseStart_2239484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239524 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2239524 : Nat := 118140960795 + 2239524 * 2 ^ 59
def prefixEnd_2239524 : Nat := 4983230072969 + 3 ^ 40 * 2239524 * 2
def baseEnd_2239524 : Nat := 1149952249279801085750623

theorem tailTrace_2239524 : CollatzResearch.WordTrace tailWord_2239524 prefixEnd_2239524 1149952249279801085750623 := by
  unfold tailWord_2239524
  simp only [CollatzResearch.WordTrace]
  refine ⟨40841075369297251546750813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54454767159063002062334417 40841075369297251546750813)
  ·
    refine ⟨15315403263486469330031555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40841075369297251546750813 15315403263486469330031555)
    ·
      refine ⟨22973104895229703995047333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15315403263486469330031555 22973104895229703995047333)
      ·
        refine ⟨4307457167855569499071375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22973104895229703995047333 4307457167855569499071375)
        ·
          refine ⟨6461185751783354248607063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307457167855569499071375 6461185751783354248607063)
          ·
            refine ⟨9691778627675031372910595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461185751783354248607063 9691778627675031372910595)
            ·
              refine ⟨14537667941512547059365893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9691778627675031372910595 14537667941512547059365893)
              ·
                refine ⟨2725812739033602573631105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14537667941512547059365893 2725812739033602573631105)
                ·
                  refine ⟨2044359554275201930223329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725812739033602573631105 2044359554275201930223329)
                  ·
                    refine ⟨1533269665706401447667497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2044359554275201930223329 1533269665706401447667497)
                    ·
                      refine ⟨1149952249279801085750623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533269665706401447667497 1149952249279801085750623)
                      ·
                        rfl

theorem cell23_2239524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2239524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239524 prefixEnd_2239524 := by exact prefixLift 2239524
  have htrace : WordTrace (prefixWord ++ tailWord_2239524) baseStart_2239524 baseEnd_2239524 := by
    simpa [prefixWord, tailWord_2239524, baseEnd_2239524] using wordTrace_append hprefix tailTrace_2239524
  have hstable : (prefixWord ++ tailWord_2239524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239524).length < 2 ^ (prefixWord ++ tailWord_2239524).sum := by decide
  have hdescent : baseEnd_2239524 < baseStart_2239524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239580 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2239580 : Nat := 118140960795 + 2239580 * 2 ^ 59
def prefixEnd_2239580 : Nat := 4983230072969 + 3 ^ 40 * 2239580 * 2
def baseEnd_2239580 : Nat := 1149981004196452866650365

theorem tailTrace_2239580 : CollatzResearch.WordTrace tailWord_2239580 prefixEnd_2239580 1149981004196452866650365 := by
  unfold tailWord_2239580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40842096613195812328770097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54456128817594416438360129 40842096613195812328770097)
  ·
    refine ⟨30631572459896859246577573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40842096613195812328770097 30631572459896859246577573)
    ·
      refine ⟨5743419836230661108733295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30631572459896859246577573 5743419836230661108733295)
      ·
        refine ⟨8615129754345991663099943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743419836230661108733295 8615129754345991663099943)
        ·
          refine ⟨12922694631518987494649915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8615129754345991663099943 12922694631518987494649915)
          ·
            refine ⟨19384041947278481241974873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12922694631518987494649915 19384041947278481241974873)
            ·
              refine ⟨14538031460458860931481155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19384041947278481241974873 14538031460458860931481155)
              ·
                refine ⟨21807047190688291397221733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14538031460458860931481155 21807047190688291397221733)
                ·
                  refine ⟨4088821348254054636979075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21807047190688291397221733 4088821348254054636979075)
                  ·
                    refine ⟨6133232022381081955468613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4088821348254054636979075 6133232022381081955468613)
                    ·
                      refine ⟨1149981004196452866650365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6133232022381081955468613 1149981004196452866650365)
                      ·
                        rfl

theorem cell23_2239580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2239580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239580 prefixEnd_2239580 := by exact prefixLift 2239580
  have htrace : WordTrace (prefixWord ++ tailWord_2239580) baseStart_2239580 baseEnd_2239580 := by
    simpa [prefixWord, tailWord_2239580, baseEnd_2239580] using wordTrace_append hprefix tailTrace_2239580
  have hstable : (prefixWord ++ tailWord_2239580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239580).length < 2 ^ (prefixWord ++ tailWord_2239580).sum := by decide
  have hdescent : baseEnd_2239580 < baseStart_2239580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239597 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_2239597 : Nat := 118140960795 + 2239597 * 2 ^ 59
def prefixEnd_2239597 : Nat := 4983230072969 + 3 ^ 40 * 2239597 * 2
def baseEnd_2239597 : Nat := 1149989733367579300137787

theorem tailTrace_2239597 : CollatzResearch.WordTrace tailWord_2239597 prefixEnd_2239597 1149989733367579300137787 := by
  unfold tailWord_2239597
  simp only [CollatzResearch.WordTrace]
  refine ⟨81684813267330036560909045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54456542178220024373939363 81684813267330036560909045)
  ·
    refine ⟨7657951243812190927585223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81684813267330036560909045 7657951243812190927585223)
    ·
      refine ⟨11486926865718286391377835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7657951243812190927585223 11486926865718286391377835)
      ·
        refine ⟨17230390298577429587066753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11486926865718286391377835 17230390298577429587066753)
        ·
          refine ⟨12922792723933072190300065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17230390298577429587066753 12922792723933072190300065)
          ·
            refine ⟨9692094542949804142725049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12922792723933072190300065 9692094542949804142725049)
            ·
              refine ⟨7269070907212353107043787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9692094542949804142725049 7269070907212353107043787)
              ·
                refine ⟨10903606360818529660565681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7269070907212353107043787 10903606360818529660565681)
                ·
                  refine ⟨8177704770613897245424261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10903606360818529660565681 8177704770613897245424261)
                  ·
                    refine ⟨1533319644490105733517049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8177704770613897245424261 1533319644490105733517049)
                    ·
                      refine ⟨1149989733367579300137787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533319644490105733517049 1149989733367579300137787)
                      ·
                        rfl

theorem cell23_2239597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_2239597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239597 prefixEnd_2239597 := by exact prefixLift 2239597
  have htrace : WordTrace (prefixWord ++ tailWord_2239597) baseStart_2239597 baseEnd_2239597 := by
    simpa [prefixWord, tailWord_2239597, baseEnd_2239597] using wordTrace_append hprefix tailTrace_2239597
  have hstable : (prefixWord ++ tailWord_2239597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239597).length < 2 ^ (prefixWord ++ tailWord_2239597).sum := by decide
  have hdescent : baseEnd_2239597 < baseStart_2239597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239683 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6]
def baseStart_2239683 : Nat := 118140960795 + 2239683 * 2 ^ 59
def prefixEnd_2239683 : Nat := 4983230072969 + 3 ^ 40 * 2239683 * 2
def baseEnd_2239683 : Nat := 1150033892703865963662391

theorem tailTrace_2239683 : CollatzResearch.WordTrace tailWord_2239683 prefixEnd_2239683 1150033892703865963662391 := by
  unfold tailWord_2239683
  simp only [CollatzResearch.WordTrace]
  refine ⟨81687949945018473248539703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54458633296678982165693135 81687949945018473248539703)
  ·
    refine ⟨122531924917527709872809555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81687949945018473248539703 122531924917527709872809555)
    ·
      refine ⟨183797887376291564809214333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122531924917527709872809555 183797887376291564809214333)
      ·
        refine ⟨68924207766109336803455375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183797887376291564809214333 68924207766109336803455375)
        ·
          refine ⟨103386311649164005205183063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68924207766109336803455375 103386311649164005205183063)
          ·
            refine ⟨155079467473746007807774595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103386311649164005205183063 155079467473746007807774595)
            ·
              refine ⟨232619201210619011711661893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155079467473746007807774595 232619201210619011711661893)
              ·
                refine ⟨43616100226991064695936605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232619201210619011711661893 43616100226991064695936605)
                ·
                  refine ⟨16356037585121649260976227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43616100226991064695936605 16356037585121649260976227)
                  ·
                    refine ⟨24534056377682473891464341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16356037585121649260976227 24534056377682473891464341)
                    ·
                      refine ⟨1150033892703865963662391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24534056377682473891464341 1150033892703865963662391)
                      ·
                        rfl

theorem cell23_2239683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_2239683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239683 prefixEnd_2239683 := by exact prefixLift 2239683
  have htrace : WordTrace (prefixWord ++ tailWord_2239683) baseStart_2239683 baseEnd_2239683 := by
    simpa [prefixWord, tailWord_2239683, baseEnd_2239683] using wordTrace_append hprefix tailTrace_2239683
  have hstable : (prefixWord ++ tailWord_2239683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239683).length < 2 ^ (prefixWord ++ tailWord_2239683).sum := by decide
  have hdescent : baseEnd_2239683 < baseStart_2239683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239727 : List Nat := [1, 1, 2, 1, 7, 1, 3, 7]
def baseStart_2239727 : Nat := 118140960795 + 2239727 * 2 ^ 59
def prefixEnd_2239727 : Nat := 4983230072969 + 3 ^ 40 * 2239727 * 2
def baseEnd_2239727 : Nat := 42594684661209770056007

theorem tailTrace_2239727 : CollatzResearch.WordTrace tailWord_2239727 prefixEnd_2239727 42594684661209770056007 := by
  unfold tailWord_2239727
  simp only [CollatzResearch.WordTrace]
  refine ⟨81689554756859068763141435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54459703171239379175427623 81689554756859068763141435)
  ·
    refine ⟨122534332135288603144712153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81689554756859068763141435 122534332135288603144712153)
    ·
      refine ⟨91900749101466452358534115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122534332135288603144712153 91900749101466452358534115)
      ·
        refine ⟨137851123652199678537801173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91900749101466452358534115 137851123652199678537801173)
        ·
          refine ⟨3230885710598429965729715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 137851123652199678537801173 3230885710598429965729715)
          ·
            refine ⟨4846328565897644948594573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230885710598429965729715 4846328565897644948594573)
            ·
              refine ⟨1817373212211616855722965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4846328565897644948594573 1817373212211616855722965)
              ·
                refine ⟨42594684661209770056007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1817373212211616855722965 42594684661209770056007)
                ·
                  rfl

theorem cell23_2239727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 7].length) (baseStart_2239727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239727 prefixEnd_2239727 := by exact prefixLift 2239727
  have htrace : WordTrace (prefixWord ++ tailWord_2239727) baseStart_2239727 baseEnd_2239727 := by
    simpa [prefixWord, tailWord_2239727, baseEnd_2239727] using wordTrace_append hprefix tailTrace_2239727
  have hstable : (prefixWord ++ tailWord_2239727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239727).length < 2 ^ (prefixWord ++ tailWord_2239727).sum := by decide
  have hdescent : baseEnd_2239727 < baseStart_2239727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239732 : List Nat := [2, 6, 1, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2239732 : Nat := 118140960795 + 2239732 * 2 ^ 59
def prefixEnd_2239732 : Nat := 4983230072969 + 3 ^ 40 * 2239732 * 2
def baseEnd_2239732 : Nat := 1150059053255936271949667

theorem tailTrace_2239732 : CollatzResearch.WordTrace tailWord_2239732 prefixEnd_2239732 1150059053255936271949667 := by
  unfold tailWord_2239732
  simp only [CollatzResearch.WordTrace]
  refine ⟨40844868560920477308536725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54459824747893969744715633 40844868560920477308536725)
  ·
    refine ⟨1914603213793147373837659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40844868560920477308536725 1914603213793147373837659)
    ·
      refine ⟨2871904820689721060756489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914603213793147373837659 2871904820689721060756489)
      ·
        refine ⟨2153928615517290795567367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2871904820689721060756489 2153928615517290795567367)
        ·
          refine ⟨3230892923275936193351051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2153928615517290795567367 3230892923275936193351051)
          ·
            refine ⟨4846339384913904290026577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230892923275936193351051 4846339384913904290026577)
            ·
              refine ⟨3634754538685428217519933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4846339384913904290026577 3634754538685428217519933)
              ·
                refine ⟨1363032952007035581569975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634754538685428217519933 1363032952007035581569975)
                ·
                  refine ⟨2044549428010553372354963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363032952007035581569975 2044549428010553372354963)
                  ·
                    refine ⟨3066824142015830058532445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044549428010553372354963 3066824142015830058532445)
                    ·
                      refine ⟨1150059053255936271949667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066824142015830058532445 1150059053255936271949667)
                      ·
                        rfl

theorem cell23_2239732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2239732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239732 prefixEnd_2239732 := by exact prefixLift 2239732
  have htrace : WordTrace (prefixWord ++ tailWord_2239732) baseStart_2239732 baseEnd_2239732 := by
    simpa [prefixWord, tailWord_2239732, baseEnd_2239732] using wordTrace_append hprefix tailTrace_2239732
  have hstable : (prefixWord ++ tailWord_2239732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239732).length < 2 ^ (prefixWord ++ tailWord_2239732).sum := by decide
  have hdescent : baseEnd_2239732 < baseStart_2239732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239737 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 3]
def baseStart_2239737 : Nat := 118140960795 + 2239737 * 2 ^ 59
def prefixEnd_2239737 : Nat := 4983230072969 + 3 ^ 40 * 2239737 * 2
def baseEnd_2239737 : Nat := 1150061620659208752387143

theorem tailTrace_2239737 : CollatzResearch.WordTrace tailWord_2239737 prefixEnd_2239737 1150061620659208752387143 := by
  unfold tailWord_2239737
  simp only [CollatzResearch.WordTrace]
  refine ⟨81689919486822840471005465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54459946324548560314003643 81689919486822840471005465)
  ·
    refine ⟨61267439615117130353254099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81689919486822840471005465 61267439615117130353254099)
    ·
      refine ⟨91901159422675695529881149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61267439615117130353254099 91901159422675695529881149)
      ·
        refine ⟨34462934783503385823705431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91901159422675695529881149 34462934783503385823705431)
        ·
          refine ⟨51694402175255078735558147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34462934783503385823705431 51694402175255078735558147)
          ·
            refine ⟨77541603262882618103337221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51694402175255078735558147 77541603262882618103337221)
            ·
              refine ⟨14539050611790490894375729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77541603262882618103337221 14539050611790490894375729)
              ·
                refine ⟨10904287958842868170781797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14539050611790490894375729 10904287958842868170781797)
                ·
                  refine ⟨2044553992283037782021587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10904287958842868170781797 2044553992283037782021587)
                  ·
                    refine ⟨3066830988424556673032381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044553992283037782021587 3066830988424556673032381)
                    ·
                      refine ⟨1150061620659208752387143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3066830988424556673032381 1150061620659208752387143)
                      ·
                        rfl

theorem cell23_2239737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_2239737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239737 prefixEnd_2239737 := by exact prefixLift 2239737
  have htrace : WordTrace (prefixWord ++ tailWord_2239737) baseStart_2239737 baseEnd_2239737 := by
    simpa [prefixWord, tailWord_2239737, baseEnd_2239737] using wordTrace_append hprefix tailTrace_2239737
  have hstable : (prefixWord ++ tailWord_2239737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239737).length < 2 ^ (prefixWord ++ tailWord_2239737).sum := by decide
  have hdescent : baseEnd_2239737 < baseStart_2239737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239781 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 1, 3, 2]
def baseStart_2239781 : Nat := 118140960795 + 2239781 * 2 ^ 59
def prefixEnd_2239781 : Nat := 4983230072969 + 3 ^ 40 * 2239781 * 2
def baseEnd_2239781 : Nat := 1150084213808006580236941

theorem tailTrace_2239781 : CollatzResearch.WordTrace tailWord_2239781 prefixEnd_2239781 1150084213808006580236941 := by
  unfold tailWord_2239781
  simp only [CollatzResearch.WordTrace]
  refine ⟨81691524298663435985607197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54461016199108957323738131 81691524298663435985607197)
  ·
    refine ⟨30634321611998788494602699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81691524298663435985607197 30634321611998788494602699)
    ·
      refine ⟨45951482417998182741904049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30634321611998788494602699 45951482417998182741904049)
      ·
        refine ⟨34463611813498637056428037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45951482417998182741904049 34463611813498637056428037)
        ·
          refine ⟨6461927215030994448080257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34463611813498637056428037 6461927215030994448080257)
          ·
            refine ⟨4846445411273245836060193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6461927215030994448080257 4846445411273245836060193)
            ·
              refine ⟨3634834058454934377045145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4846445411273245836060193 3634834058454934377045145)
              ·
                refine ⟨2726125543841200782783859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3634834058454934377045145 2726125543841200782783859)
                ·
                  refine ⟨4089188315761801174175789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726125543841200782783859 4089188315761801174175789)
                  ·
                    refine ⟨1533445618410675440315921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4089188315761801174175789 1533445618410675440315921)
                    ·
                      refine ⟨1150084213808006580236941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533445618410675440315921 1150084213808006580236941)
                      ·
                        rfl

theorem cell23_2239781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_2239781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239781 prefixEnd_2239781 := by exact prefixLift 2239781
  have htrace : WordTrace (prefixWord ++ tailWord_2239781) baseStart_2239781 baseEnd_2239781 := by
    simpa [prefixWord, tailWord_2239781, baseEnd_2239781] using wordTrace_append hprefix tailTrace_2239781
  have hstable : (prefixWord ++ tailWord_2239781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239781).length < 2 ^ (prefixWord ++ tailWord_2239781).sum := by decide
  have hdescent : baseEnd_2239781 < baseStart_2239781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239797 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2239797 : Nat := 118140960795 + 2239797 * 2 ^ 59
def prefixEnd_2239797 : Nat := 4983230072969 + 3 ^ 40 * 2239797 * 2
def baseEnd_2239797 : Nat := 1150092429498478517636867

theorem tailTrace_2239797 : CollatzResearch.WordTrace tailWord_2239797 prefixEnd_2239797 1150092429498478517636867 := by
  unfold tailWord_2239797
  simp only [CollatzResearch.WordTrace]
  refine ⟨81692107866605470718189645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54461405244403647145459763 81692107866605470718189645)
  ·
    refine ⟨30634540449977051519321117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81692107866605470718189645 30634540449977051519321117)
    ·
      refine ⟨11487952668741394319745419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30634540449977051519321117 11487952668741394319745419)
      ·
        refine ⟨17231929003112091479618129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11487952668741394319745419 17231929003112091479618129)
        ·
          refine ⟨12923946752334068609713597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17231929003112091479618129 12923946752334068609713597)
          ·
            refine ⟨4846480032125275728642599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12923946752334068609713597 4846480032125275728642599)
            ·
              refine ⟨7269720048187913592963899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846480032125275728642599 7269720048187913592963899)
              ·
                refine ⟨10904580072281870389445849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7269720048187913592963899 10904580072281870389445849)
                ·
                  refine ⟨8178435054211402792084387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10904580072281870389445849 8178435054211402792084387)
                  ·
                    refine ⟨12267652581317104188126581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8178435054211402792084387 12267652581317104188126581)
                    ·
                      refine ⟨1150092429498478517636867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12267652581317104188126581 1150092429498478517636867)
                      ·
                        rfl

theorem cell23_2239797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2239797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239797 prefixEnd_2239797 := by exact prefixLift 2239797
  have htrace : WordTrace (prefixWord ++ tailWord_2239797) baseStart_2239797 baseEnd_2239797 := by
    simpa [prefixWord, tailWord_2239797, baseEnd_2239797] using wordTrace_append hprefix tailTrace_2239797
  have hstable : (prefixWord ++ tailWord_2239797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239797).length < 2 ^ (prefixWord ++ tailWord_2239797).sum := by decide
  have hdescent : baseEnd_2239797 < baseStart_2239797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239817 : List Nat := [1, 2, 1, 1, 2, 3, 2, 6, 5]
def baseStart_2239817 : Nat := 118140960795 + 2239817 * 2 ^ 59
def prefixEnd_2239817 : Nat := 4983230072969 + 3 ^ 40 * 2239817 * 2
def baseEnd_2239817 : Nat := 127789188790174271042975

theorem tailTrace_2239817 : CollatzResearch.WordTrace tailWord_2239817 prefixEnd_2239817 127789188790174271042975 := by
  unfold tailWord_2239817
  simp only [CollatzResearch.WordTrace]
  refine ⟨81692837326533014133917705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54461891551022009422611803 81692837326533014133917705)
  ·
    refine ⟨61269627994899760600438279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81692837326533014133917705 61269627994899760600438279)
    ·
      refine ⟨91904441992349640900657419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61269627994899760600438279 91904441992349640900657419)
      ·
        refine ⟨137856662988524461350986129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91904441992349640900657419 137856662988524461350986129)
        ·
          refine ⟨103392497241393346013239597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137856662988524461350986129 103392497241393346013239597)
          ·
            refine ⟨38772186465522504754964849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103392497241393346013239597 38772186465522504754964849)
            ·
              refine ⟨29079139849141878566223637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38772186465522504754964849 29079139849141878566223637)
              ·
                refine ⟨1363084680428525557791733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29079139849141878566223637 1363084680428525557791733)
                ·
                  refine ⟨127789188790174271042975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1363084680428525557791733 127789188790174271042975)
                  ·
                    rfl

theorem cell23_2239817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 5].length) (baseStart_2239817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239817 prefixEnd_2239817 := by exact prefixLift 2239817
  have htrace : WordTrace (prefixWord ++ tailWord_2239817) baseStart_2239817 baseEnd_2239817 := by
    simpa [prefixWord, tailWord_2239817, baseEnd_2239817] using wordTrace_append hprefix tailTrace_2239817
  have hstable : (prefixWord ++ tailWord_2239817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239817).length < 2 ^ (prefixWord ++ tailWord_2239817).sum := by decide
  have hdescent : baseEnd_2239817 < baseStart_2239817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239867 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 4]
def baseStart_2239867 : Nat := 118140960795 + 2239867 * 2 ^ 59
def prefixEnd_2239867 : Nat := 4983230072969 + 3 ^ 40 * 2239867 * 2
def baseEnd_2239867 : Nat := 1150128373144293243761545

theorem tailTrace_2239867 : CollatzResearch.WordTrace tailWord_2239867 prefixEnd_2239867 1150128373144293243761545 := by
  unfold tailWord_2239867
  simp only [CollatzResearch.WordTrace]
  refine ⟨81694660976351872673237855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54463107317567915115491903 81694660976351872673237855)
  ·
    refine ⟨122541991464527809009856783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81694660976351872673237855 122541991464527809009856783)
    ·
      refine ⟨183812987196791713514785175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122541991464527809009856783 183812987196791713514785175)
      ·
        refine ⟨275719480795187570272177763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183812987196791713514785175 275719480795187570272177763)
        ·
          refine ⟨413579221192781355408266645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275719480795187570272177763 413579221192781355408266645)
          ·
            refine ⟨19386525993411626034762499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 413579221192781355408266645 19386525993411626034762499)
            ·
              refine ⟨29079788990117439052143749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19386525993411626034762499 29079788990117439052143749)
              ·
                refine ⟨5452460435647019822276953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29079788990117439052143749 5452460435647019822276953)
                ·
                  refine ⟨4089345326735264866707715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5452460435647019822276953 4089345326735264866707715)
                  ·
                    refine ⟨6134017990102897300061573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4089345326735264866707715 6134017990102897300061573)
                    ·
                      refine ⟨1150128373144293243761545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6134017990102897300061573 1150128373144293243761545)
                      ·
                        rfl

theorem cell23_2239867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 4].length) (baseStart_2239867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239867 prefixEnd_2239867 := by exact prefixLift 2239867
  have htrace : WordTrace (prefixWord ++ tailWord_2239867) baseStart_2239867 baseEnd_2239867 := by
    simpa [prefixWord, tailWord_2239867, baseEnd_2239867] using wordTrace_append hprefix tailTrace_2239867
  have hstable : (prefixWord ++ tailWord_2239867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239867).length < 2 ^ (prefixWord ++ tailWord_2239867).sum := by decide
  have hdescent : baseEnd_2239867 < baseStart_2239867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239884 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 2, 4, 2]
def baseStart_2239884 : Nat := 118140960795 + 2239884 * 2 ^ 59
def prefixEnd_2239884 : Nat := 4983230072969 + 3 ^ 40 * 2239884 * 2
def baseEnd_2239884 : Nat := 1150137102315419677248967

theorem tailTrace_2239884 : CollatzResearch.WordTrace tailWord_2239884 prefixEnd_2239884 1150137102315419677248967 := by
  unfold tailWord_2239884
  simp only [CollatzResearch.WordTrace]
  refine ⟨40847640508645142288303353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54463520678193523051071137 40847640508645142288303353)
  ·
    refine ⟨30635730381483856716227515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40847640508645142288303353 30635730381483856716227515)
    ·
      refine ⟨45953595572225785074341273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30635730381483856716227515 45953595572225785074341273)
      ·
        refine ⟨34465196679169338805755955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45953595572225785074341273 34465196679169338805755955)
        ·
          refine ⟨51697795018754008208633933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34465196679169338805755955 51697795018754008208633933)
          ·
            refine ⟨19386673132032753078237725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51697795018754008208633933 19386673132032753078237725)
            ·
              refine ⟨7270002424512282404339147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19386673132032753078237725 7270002424512282404339147)
              ·
                refine ⟨10905003636768423606508721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270002424512282404339147 10905003636768423606508721)
                ·
                  refine ⟨8178752727576317704881541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10905003636768423606508721 8178752727576317704881541)
                  ·
                    refine ⟨1533516136420559569665289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8178752727576317704881541 1533516136420559569665289)
                    ·
                      refine ⟨1150137102315419677248967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533516136420559569665289 1150137102315419677248967)
                      ·
                        rfl

theorem cell23_2239884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_2239884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239884 prefixEnd_2239884 := by exact prefixLift 2239884
  have htrace : WordTrace (prefixWord ++ tailWord_2239884) baseStart_2239884 baseEnd_2239884 := by
    simpa [prefixWord, tailWord_2239884, baseEnd_2239884] using wordTrace_append hprefix tailTrace_2239884
  have hstable : (prefixWord ++ tailWord_2239884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239884).length < 2 ^ (prefixWord ++ tailWord_2239884).sum := by decide
  have hdescent : baseEnd_2239884 < baseStart_2239884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239901 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2239901 : Nat := 118140960795 + 2239901 * 2 ^ 59
def prefixEnd_2239901 : Nat := 4983230072969 + 3 ^ 40 * 2239901 * 2
def baseEnd_2239901 : Nat := 1150145831486546110736389

theorem tailTrace_2239901 : CollatzResearch.WordTrace tailWord_2239901 prefixEnd_2239901 1150145831486546110736389 := by
  unfold tailWord_2239901
  simp only [CollatzResearch.WordTrace]
  refine ⟨81695901058228696479975557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54463934038819130986650371 81695901058228696479975557)
  ·
    refine ⟨15317981448417880589995417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81695901058228696479975557 15317981448417880589995417)
    ·
      refine ⟨11488486086313410442496563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15317981448417880589995417 11488486086313410442496563)
      ·
        refine ⟨17232729129470115663744845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11488486086313410442496563 17232729129470115663744845)
        ·
          refine ⟨6462273423551293373904317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17232729129470115663744845 6462273423551293373904317)
          ·
            refine ⟨2423352533831735015214119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6462273423551293373904317 2423352533831735015214119)
            ·
              refine ⟨3635028800747602522821179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423352533831735015214119 3635028800747602522821179)
              ·
                refine ⟨5452543201121403784231769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635028800747602522821179 5452543201121403784231769)
                ·
                  refine ⟨4089407400841052838173827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5452543201121403784231769 4089407400841052838173827)
                  ·
                    refine ⟨6134111101261579257260741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4089407400841052838173827 6134111101261579257260741)
                    ·
                      refine ⟨1150145831486546110736389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6134111101261579257260741 1150145831486546110736389)
                      ·
                        rfl

theorem cell23_2239901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2239901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239901 prefixEnd_2239901 := by exact prefixLift 2239901
  have htrace : WordTrace (prefixWord ++ tailWord_2239901) baseStart_2239901 baseEnd_2239901 := by
    simpa [prefixWord, tailWord_2239901, baseEnd_2239901] using wordTrace_append hprefix tailTrace_2239901
  have hstable : (prefixWord ++ tailWord_2239901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239901).length < 2 ^ (prefixWord ++ tailWord_2239901).sum := by decide
  have hdescent : baseEnd_2239901 < baseStart_2239901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239944 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_2239944 : Nat := 118140960795 + 2239944 * 2 ^ 59
def prefixEnd_2239944 : Nat := 4983230072969 + 3 ^ 40 * 2239944 * 2
def baseEnd_2239944 : Nat := 1150167911154689442498691

theorem tailTrace_2239944 : CollatzResearch.WordTrace tailWord_2239944 prefixEnd_2239944 1150167911154689442498691 := by
  unfold tailWord_2239944
  simp only [CollatzResearch.WordTrace]
  refine ⟨40848734698536457411895443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54464979598048609882527257 40848734698536457411895443)
  ·
    refine ⟨61273102047804686117843165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40848734698536457411895443 61273102047804686117843165)
    ·
      refine ⟨22977413267926757294191187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61273102047804686117843165 22977413267926757294191187)
      ·
        refine ⟨34466119901890135941286781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22977413267926757294191187 34466119901890135941286781)
        ·
          refine ⟨12924794963208800977982543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34466119901890135941286781 12924794963208800977982543)
          ·
            refine ⟨19387192444813201466973815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12924794963208800977982543 19387192444813201466973815)
            ·
              refine ⟨29080788667219802200460723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19387192444813201466973815 29080788667219802200460723)
              ·
                refine ⟨43621183000829703300691085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29080788667219802200460723 43621183000829703300691085)
                ·
                  refine ⟨16357943625311138737759157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43621183000829703300691085 16357943625311138737759157)
                  ·
                    refine ⟨1533557214872919256664921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16357943625311138737759157 1533557214872919256664921)
                    ·
                      refine ⟨1150167911154689442498691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533557214872919256664921 1150167911154689442498691)
                      ·
                        rfl

theorem cell23_2239944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_2239944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239944 prefixEnd_2239944 := by exact prefixLift 2239944
  have htrace : WordTrace (prefixWord ++ tailWord_2239944) baseStart_2239944 baseEnd_2239944 := by
    simpa [prefixWord, tailWord_2239944, baseEnd_2239944] using wordTrace_append hprefix tailTrace_2239944
  have hstable : (prefixWord ++ tailWord_2239944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239944).length < 2 ^ (prefixWord ++ tailWord_2239944).sum := by decide
  have hdescent : baseEnd_2239944 < baseStart_2239944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239967 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 3, 6]
def baseStart_2239967 : Nat := 118140960795 + 2239967 * 2 ^ 59
def prefixEnd_2239967 : Nat := 4983230072969 + 3 ^ 40 * 2239967 * 2
def baseEnd_2239967 : Nat := 383393240403247617503695

theorem tailTrace_2239967 : CollatzResearch.WordTrace tailWord_2239967 prefixEnd_2239967 383393240403247617503695 := by
  unfold tailWord_2239967
  simp only [CollatzResearch.WordTrace]
  refine ⟨81698308275989589751878155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54465538850659726501252103 81698308275989589751878155)
  ·
    refine ⟨122547462413984384627817233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81698308275989589751878155 122547462413984384627817233)
    ·
      refine ⟨91910596810488288470862925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122547462413984384627817233 91910596810488288470862925)
      ·
        refine ⟨34466473803933108176573597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91910596810488288470862925 34466473803933108176573597)
        ·
          refine ⟨12924927676474915566215099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34466473803933108176573597 12924927676474915566215099)
          ·
            refine ⟨19387391514712373349322649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12924927676474915566215099 19387391514712373349322649)
            ·
              refine ⟨14540543636034280011991987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19387391514712373349322649 14540543636034280011991987)
              ·
                refine ⟨21810815454051420017987981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14540543636034280011991987 21810815454051420017987981)
                ·
                  refine ⟨8179055795269282506745493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21810815454051420017987981 8179055795269282506745493)
                  ·
                    refine ⟨383393240403247617503695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8179055795269282506745493 383393240403247617503695)
                    ·
                      rfl

theorem cell23_2239967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_2239967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239967 prefixEnd_2239967 := by exact prefixLift 2239967
  have htrace : WordTrace (prefixWord ++ tailWord_2239967) baseStart_2239967 baseEnd_2239967 := by
    simpa [prefixWord, tailWord_2239967, baseEnd_2239967] using wordTrace_append hprefix tailTrace_2239967
  have hstable : (prefixWord ++ tailWord_2239967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239967).length < 2 ^ (prefixWord ++ tailWord_2239967).sum := by decide
  have hdescent : baseEnd_2239967 < baseStart_2239967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239977 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 3]
def baseStart_2239977 : Nat := 118140960795 + 2239977 * 2 ^ 59
def prefixEnd_2239977 : Nat := 4983230072969 + 3 ^ 40 * 2239977 * 2
def baseEnd_2239977 : Nat := 1150184856016287813386039

theorem tailTrace_2239977 : CollatzResearch.WordTrace tailWord_2239977 prefixEnd_2239977 1150184856016287813386039 := by
  unfold tailWord_2239977
  simp only [CollatzResearch.WordTrace]
  refine ⟨81698673005953361459742185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54465782003968907639828123 81698673005953361459742185)
  ·
    refine ⟨61274004754465021094806639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81698673005953361459742185 61274004754465021094806639)
    ·
      refine ⟨91911007131697531642209959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61274004754465021094806639 91911007131697531642209959)
      ·
        refine ⟨137866510697546297463314939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91911007131697531642209959 137866510697546297463314939)
        ·
          refine ⟨206799766046319446194972409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137866510697546297463314939 206799766046319446194972409)
          ·
            refine ⟨155099824534739584646229307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206799766046319446194972409 155099824534739584646229307)
            ·
              refine ⟨232649736802109376969343961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155099824534739584646229307 232649736802109376969343961)
              ·
                refine ⟨174487302601582032727007971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232649736802109376969343961 174487302601582032727007971)
                ·
                  refine ⟨261730953902373049090511957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174487302601582032727007971 261730953902373049090511957)
                  ·
                    refine ⟨3067159616043434169029437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 261730953902373049090511957 3067159616043434169029437)
                    ·
                      refine ⟨1150184856016287813386039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067159616043434169029437 1150184856016287813386039)
                      ·
                        rfl

theorem cell23_2239977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_2239977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239977 prefixEnd_2239977 := by exact prefixLift 2239977
  have htrace : WordTrace (prefixWord ++ tailWord_2239977) baseStart_2239977 baseEnd_2239977 := by
    simpa [prefixWord, tailWord_2239977, baseEnd_2239977] using wordTrace_append hprefix tailTrace_2239977
  have hstable : (prefixWord ++ tailWord_2239977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239977).length < 2 ^ (prefixWord ++ tailWord_2239977).sum := by decide
  have hdescent : baseEnd_2239977 < baseStart_2239977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239978 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_2239978 : Nat := 118140960795 + 2239978 * 2 ^ 59
def prefixEnd_2239978 : Nat := 4983230072969 + 3 ^ 40 * 2239978 * 2
def baseEnd_2239978 : Nat := 1150185369496942309473535

theorem tailTrace_2239978 : CollatzResearch.WordTrace tailWord_2239978 prefixEnd_2239978 1150185369496942309473535 := by
  unfold tailWord_2239978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20424677369737434657632147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54465806319299825753685725 20424677369737434657632147)
  ·
    refine ⟨30637016054606151986448221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20424677369737434657632147 30637016054606151986448221)
    ·
      refine ⟨11488881020477306994918083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30637016054606151986448221 11488881020477306994918083)
      ·
        refine ⟨17233321530715960492377125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11488881020477306994918083 17233321530715960492377125)
        ·
          refine ⟨3231247787009242592320711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17233321530715960492377125 3231247787009242592320711)
          ·
            refine ⟨4846871680513863888481067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231247787009242592320711 4846871680513863888481067)
            ·
              refine ⟨7270307520770795832721601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846871680513863888481067 7270307520770795832721601)
              ·
                refine ⟨5452730640578096874541201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7270307520770795832721601 5452730640578096874541201)
                ·
                  refine ⟨4089547980433572655905901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5452730640578096874541201 4089547980433572655905901)
                  ·
                    refine ⟨1533580492662589745964713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4089547980433572655905901 1533580492662589745964713)
                    ·
                      refine ⟨1150185369496942309473535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533580492662589745964713 1150185369496942309473535)
                      ·
                        rfl

theorem cell23_2239978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_2239978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239978 prefixEnd_2239978 := by exact prefixLift 2239978
  have htrace : WordTrace (prefixWord ++ tailWord_2239978) baseStart_2239978 baseEnd_2239978 := by
    simpa [prefixWord, tailWord_2239978, baseEnd_2239978] using wordTrace_append hprefix tailTrace_2239978
  have hstable : (prefixWord ++ tailWord_2239978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239978).length < 2 ^ (prefixWord ++ tailWord_2239978).sum := by decide
  have hdescent : baseEnd_2239978 < baseStart_2239978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239984 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 4, 4]
def baseStart_2239984 : Nat := 118140960795 + 2239984 * 2 ^ 59
def prefixEnd_2239984 : Nat := 4983230072969 + 3 ^ 40 * 2239984 * 2
def baseEnd_2239984 : Nat := 383396150126956428666169

theorem tailTrace_2239984 : CollatzResearch.WordTrace tailWord_2239984 prefixEnd_2239984 383396150126956428666169 := by
  unfold tailWord_2239984
  simp only [CollatzResearch.WordTrace]
  refine ⟨40849464158464000827623503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54465952211285334436831337 40849464158464000827623503)
  ·
    refine ⟨61274196237696001241435255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40849464158464000827623503 61274196237696001241435255)
    ·
      refine ⟨91911294356544001862152883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61274196237696001241435255 91911294356544001862152883)
      ·
        refine ⟨137866941534816002793229325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91911294356544001862152883 137866941534816002793229325)
        ·
          refine ⟨51700103075556001047460997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137866941534816002793229325 51700103075556001047460997)
          ·
            refine ⟨9693769326666750196398937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51700103075556001047460997 9693769326666750196398937)
            ·
              refine ⟨7270326995000062647299203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9693769326666750196398937 7270326995000062647299203)
              ·
                refine ⟨10905490492500093970948805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270326995000062647299203 10905490492500093970948805)
                ·
                  refine ⟨2044779467343767619552901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10905490492500093970948805 2044779467343767619552901)
                  ·
                    refine ⟨383396150126956428666169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2044779467343767619552901 383396150126956428666169)
                    ·
                      rfl

theorem cell23_2239984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_2239984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239984 prefixEnd_2239984 := by exact prefixLift 2239984
  have htrace : WordTrace (prefixWord ++ tailWord_2239984) baseStart_2239984 baseEnd_2239984 := by
    simpa [prefixWord, tailWord_2239984, baseEnd_2239984] using wordTrace_append hprefix tailTrace_2239984
  have hstable : (prefixWord ++ tailWord_2239984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239984).length < 2 ^ (prefixWord ++ tailWord_2239984).sum := by decide
  have hdescent : baseEnd_2239984 < baseStart_2239984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239985 : List Nat := [1, 2, 2, 2, 3, 3, 3, 2, 1, 1, 3]
def baseStart_2239985 : Nat := 118140960795 + 2239985 * 2 ^ 59
def prefixEnd_2239985 : Nat := 4983230072969 + 3 ^ 40 * 2239985 * 2
def baseEnd_2239985 : Nat := 1150188963861523782086003

theorem tailTrace_2239985 : CollatzResearch.WordTrace tailWord_2239985 prefixEnd_2239985 1150188963861523782086003 := by
  unfold tailWord_2239985
  simp only [CollatzResearch.WordTrace]
  refine ⟨81698964789924378826033409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54465976526616252550688939 81698964789924378826033409)
  ·
    refine ⟨61274223592443284119525057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81698964789924378826033409 61274223592443284119525057)
    ·
      refine ⟨45955667694332463089643793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61274223592443284119525057 45955667694332463089643793)
      ·
        refine ⟨34466750770749347317232845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45955667694332463089643793 34466750770749347317232845)
        ·
          refine ⟨12925031539031005243962317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34466750770749347317232845 12925031539031005243962317)
          ·
            refine ⟨4846886827136626966485869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12925031539031005243962317 4846886827136626966485869)
            ·
              refine ⟨1817582560176235112432201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4846886827136626966485869 1817582560176235112432201)
              ·
                refine ⟨1363186920132176334324151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817582560176235112432201 1363186920132176334324151)
                ·
                  refine ⟨2044780380198264501486227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363186920132176334324151 2044780380198264501486227)
                  ·
                    refine ⟨3067170570297396752229341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044780380198264501486227 3067170570297396752229341)
                    ·
                      refine ⟨1150188963861523782086003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067170570297396752229341 1150188963861523782086003)
                      ·
                        rfl

theorem cell23_2239985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_2239985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239985 prefixEnd_2239985 := by exact prefixLift 2239985
  have htrace : WordTrace (prefixWord ++ tailWord_2239985) baseStart_2239985 baseEnd_2239985 := by
    simpa [prefixWord, tailWord_2239985, baseEnd_2239985] using wordTrace_append hprefix tailTrace_2239985
  have hstable : (prefixWord ++ tailWord_2239985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239985).length < 2 ^ (prefixWord ++ tailWord_2239985).sum := by decide
  have hdescent : baseEnd_2239985 < baseStart_2239985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239987 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4]
def baseStart_2239987 : Nat := 118140960795 + 2239987 * 2 ^ 59
def prefixEnd_2239987 : Nat := 4983230072969 + 3 ^ 40 * 2239987 * 2
def baseEnd_2239987 : Nat := 1150189990822832774260993

theorem tailTrace_2239987 : CollatzResearch.WordTrace tailWord_2239987 prefixEnd_2239987 1150189990822832774260993 := by
  unfold tailWord_2239987
  simp only [CollatzResearch.WordTrace]
  refine ⟨81699037735917133167606215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54466025157278088778404143 81699037735917133167606215)
  ·
    refine ⟨122548556603875699751409323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81699037735917133167606215 122548556603875699751409323)
    ·
      refine ⟨183822834905813549627113985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122548556603875699751409323 183822834905813549627113985)
      ·
        refine ⟨137867126179360162220335489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183822834905813549627113985 137867126179360162220335489)
        ·
          refine ⟨103400344634520121665251617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137867126179360162220335489 103400344634520121665251617)
          ·
            refine ⟨77550258475890091248938713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103400344634520121665251617 77550258475890091248938713)
            ·
              refine ⟨58162693856917568436704035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77550258475890091248938713 58162693856917568436704035)
              ·
                refine ⟨87244040785376352655056053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58162693856917568436704035 87244040785376352655056053)
                ·
                  refine ⟨8179128823629033061411505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87244040785376352655056053 8179128823629033061411505)
                  ·
                    refine ⟨6134346617721774796058629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8179128823629033061411505 6134346617721774796058629)
                    ·
                      refine ⟨1150189990822832774260993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6134346617721774796058629 1150189990822832774260993)
                      ·
                        rfl

theorem cell23_2239987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_2239987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239987 prefixEnd_2239987 := by exact prefixLift 2239987
  have htrace : WordTrace (prefixWord ++ tailWord_2239987) baseStart_2239987 baseEnd_2239987 := by
    simpa [prefixWord, tailWord_2239987, baseEnd_2239987] using wordTrace_append hprefix tailTrace_2239987
  have hstable : (prefixWord ++ tailWord_2239987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239987).length < 2 ^ (prefixWord ++ tailWord_2239987).sum := by decide
  have hdescent : baseEnd_2239987 < baseStart_2239987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239991 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 3, 2, 2]
def baseStart_2239991 : Nat := 118140960795 + 2239991 * 2 ^ 59
def prefixEnd_2239991 : Nat := 4983230072969 + 3 ^ 40 * 2239991 * 2
def baseEnd_2239991 : Nat := 1150192044745450758610975

theorem tailTrace_2239991 : CollatzResearch.WordTrace tailWord_2239991 prefixEnd_2239991 1150192044745450758610975 := by
  unfold tailWord_2239991
  simp only [CollatzResearch.WordTrace]
  refine ⟨81699183627902641850751827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54466122418601761233834551 81699183627902641850751827)
  ·
    refine ⟨122548775441853962776127741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81699183627902641850751827 122548775441853962776127741)
    ·
      refine ⟨45955790790695236041047903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122548775441853962776127741 45955790790695236041047903)
      ·
        refine ⟨68933686186042854061571855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45955790790695236041047903 68933686186042854061571855)
        ·
          refine ⟨103400529279064281092357783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68933686186042854061571855 103400529279064281092357783)
          ·
            refine ⟨155100793918596421638536675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103400529279064281092357783 155100793918596421638536675)
            ·
              refine ⟨232651190877894632457805013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155100793918596421638536675 232651190877894632457805013)
              ·
                refine ⟨5452762286200655448229805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232651190877894632457805013 5452762286200655448229805)
                ·
                  refine ⟨2044785857325245793086177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5452762286200655448229805 2044785857325245793086177)
                  ·
                    refine ⟨1533589392993934344814633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2044785857325245793086177 1533589392993934344814633)
                    ·
                      refine ⟨1150192044745450758610975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533589392993934344814633 1150192044745450758610975)
                      ·
                        rfl

theorem cell23_2239991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_2239991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239991 prefixEnd_2239991 := by exact prefixLift 2239991
  have htrace : WordTrace (prefixWord ++ tailWord_2239991) baseStart_2239991 baseEnd_2239991 := by
    simpa [prefixWord, tailWord_2239991, baseEnd_2239991] using wordTrace_append hprefix tailTrace_2239991
  have hstable : (prefixWord ++ tailWord_2239991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239991).length < 2 ^ (prefixWord ++ tailWord_2239991).sum := by decide
  have hdescent : baseEnd_2239991 < baseStart_2239991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239994 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_2239994 : Nat := 118140960795 + 2239994 * 2 ^ 59
def prefixEnd_2239994 : Nat := 4983230072969 + 3 ^ 40 * 2239994 * 2
def baseEnd_2239994 : Nat := 1150193585187414246873461

theorem tailTrace_2239994 : CollatzResearch.WordTrace tailWord_2239994 prefixEnd_2239994 1150193585187414246873461 := by
  unfold tailWord_2239994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20424823261722943340777759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54466195364594515575407357 20424823261722943340777759)
  ·
    refine ⟨30637234892584415011166639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20424823261722943340777759 30637234892584415011166639)
    ·
      refine ⟨45955852338876622516749959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30637234892584415011166639 45955852338876622516749959)
      ·
        refine ⟨68933778508314933775124939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45955852338876622516749959 68933778508314933775124939)
        ·
          refine ⟨103400667762472400662687409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68933778508314933775124939 103400667762472400662687409)
          ·
            refine ⟨77550500821854300497015557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103400667762472400662687409 77550500821854300497015557)
            ·
              refine ⟨14540718904097681343190417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77550500821854300497015557 14540718904097681343190417)
              ·
                refine ⟨10905539178073261007392813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14540718904097681343190417 10905539178073261007392813)
                ·
                  refine ⟨4089577191777472877772305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10905539178073261007392813 4089577191777472877772305)
                  ·
                    refine ⟨3067182893833104658329229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089577191777472877772305 3067182893833104658329229)
                    ·
                      refine ⟨1150193585187414246873461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067182893833104658329229 1150193585187414246873461)
                      ·
                        rfl

theorem cell23_2239994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_2239994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239994 prefixEnd_2239994 := by exact prefixLift 2239994
  have htrace : WordTrace (prefixWord ++ tailWord_2239994) baseStart_2239994 baseEnd_2239994 := by
    simpa [prefixWord, tailWord_2239994, baseEnd_2239994] using wordTrace_append hprefix tailTrace_2239994
  have hstable : (prefixWord ++ tailWord_2239994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239994).length < 2 ^ (prefixWord ++ tailWord_2239994).sum := by decide
  have hdescent : baseEnd_2239994 < baseStart_2239994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239997 : List Nat := [1, 4, 1, 1, 1, 4, 1, 10]
def baseStart_2239997 : Nat := 118140960795 + 2239997 * 2 ^ 59
def prefixEnd_2239997 : Nat := 4983230072969 + 3 ^ 40 * 2239997 * 2
def baseEnd_2239997 : Nat := 42599819467754730930961

theorem tailTrace_2239997 : CollatzResearch.WordTrace tailWord_2239997 prefixEnd_2239997 42599819467754730930961 := by
  unfold tailWord_2239997
  simp only [CollatzResearch.WordTrace]
  refine ⟨81699402465880904875470245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54466268310587269916980163 81699402465880904875470245)
  ·
    refine ⟨15318637962352669664150671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81699402465880904875470245 15318637962352669664150671)
    ·
      refine ⟨22977956943529004496226007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15318637962352669664150671 22977956943529004496226007)
      ·
        refine ⟨34466935415293506744339011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22977956943529004496226007 34466935415293506744339011)
        ·
          refine ⟨51700403122940260116508517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34466935415293506744339011 51700403122940260116508517)
          ·
            refine ⟨9693825585551298771845347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51700403122940260116508517 9693825585551298771845347)
            ·
              refine ⟨14540738378326948157768021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9693825585551298771845347 14540738378326948157768021)
              ·
                refine ⟨42599819467754730930961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14540738378326948157768021 42599819467754730930961)
                ·
                  rfl

theorem cell23_2239997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 10].length) (baseStart_2239997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2239997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2239997 prefixEnd_2239997 := by exact prefixLift 2239997
  have htrace : WordTrace (prefixWord ++ tailWord_2239997) baseStart_2239997 baseEnd_2239997 := by
    simpa [prefixWord, tailWord_2239997, baseEnd_2239997] using wordTrace_append hprefix tailTrace_2239997
  have hstable : (prefixWord ++ tailWord_2239997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239997).length < 2 ^ (prefixWord ++ tailWord_2239997).sum := by decide
  have hdescent : baseEnd_2239997 < baseStart_2239997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240011 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 3]
def baseStart_2240011 : Nat := 118140960795 + 2240011 * 2 ^ 59
def prefixEnd_2240011 : Nat := 4983230072969 + 3 ^ 40 * 2240011 * 2
def baseEnd_2240011 : Nat := 1150202314358540680360883

theorem tailTrace_2240011 : CollatzResearch.WordTrace tailWord_2240011 prefixEnd_2240011 1150202314358540680360883 := by
  unfold tailWord_2240011
  simp only [CollatzResearch.WordTrace]
  refine ⟨81699913087830185266479887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54466608725220123510986591 81699913087830185266479887)
  ·
    refine ⟨122549869631745277899719831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81699913087830185266479887 122549869631745277899719831)
    ·
      refine ⟨183824804447617916849579747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122549869631745277899719831 183824804447617916849579747)
      ·
        refine ⟨275737206671426875274369621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183824804447617916849579747 275737206671426875274369621)
        ·
          refine ⟨3231295390680783694621519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 275737206671426875274369621 3231295390680783694621519)
          ·
            refine ⟨4846943086021175541932279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231295390680783694621519 4846943086021175541932279)
            ·
              refine ⟨7270414629031763312898419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846943086021175541932279 7270414629031763312898419)
              ·
                refine ⟨10905621943547644969347629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270414629031763312898419 10905621943547644969347629)
                ·
                  refine ⟨4089608228830366863505361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10905621943547644969347629 4089608228830366863505361)
                  ·
                    refine ⟨3067206171622775147629021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089608228830366863505361 3067206171622775147629021)
                    ·
                      refine ⟨1150202314358540680360883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067206171622775147629021 1150202314358540680360883)
                      ·
                        rfl

theorem cell23_2240011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 3].length) (baseStart_2240011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240011 prefixEnd_2240011 := by exact prefixLift 2240011
  have htrace : WordTrace (prefixWord ++ tailWord_2240011) baseStart_2240011 baseEnd_2240011 := by
    simpa [prefixWord, tailWord_2240011, baseEnd_2240011] using wordTrace_append hprefix tailTrace_2240011
  have hstable : (prefixWord ++ tailWord_2240011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240011).length < 2 ^ (prefixWord ++ tailWord_2240011).sum := by decide
  have hdescent : baseEnd_2240011 < baseStart_2240011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240028 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_2240028 : Nat := 118140960795 + 2240028 * 2 ^ 59
def prefixEnd_2240028 : Nat := 4983230072969 + 3 ^ 40 * 2240028 * 2
def baseEnd_2240028 : Nat := 1150211043529667113848305

theorem tailTrace_2240028 : CollatzResearch.WordTrace tailWord_2240028 prefixEnd_2240028 1150211043529667113848305 := by
  unfold tailWord_2240028
  simp only [CollatzResearch.WordTrace]
  refine ⟨40850266564384298584924369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54467022085845731446565825 40850266564384298584924369)
  ·
    refine ⟨30637699923288223938693277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40850266564384298584924369 30637699923288223938693277)
    ·
      refine ⟨11489137471233083977009979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30637699923288223938693277 11489137471233083977009979)
      ·
        refine ⟨17233706206849625965514969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11489137471233083977009979 17233706206849625965514969)
        ·
          refine ⟨12925279655137219474136227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17233706206849625965514969 12925279655137219474136227)
          ·
            refine ⟨19387919482705829211204341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12925279655137219474136227 19387919482705829211204341)
            ·
              refine ⟨1817617451503671488550407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19387919482705829211204341 1817617451503671488550407)
              ·
                refine ⟨2726426177255507232825611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817617451503671488550407 2726426177255507232825611)
                ·
                  refine ⟨4089639265883260849238417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726426177255507232825611 4089639265883260849238417)
                  ·
                    refine ⟨3067229449412445636928813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089639265883260849238417 3067229449412445636928813)
                    ·
                      refine ⟨1150211043529667113848305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067229449412445636928813 1150211043529667113848305)
                      ·
                        rfl

theorem cell23_2240028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_2240028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240028 prefixEnd_2240028 := by exact prefixLift 2240028
  have htrace : WordTrace (prefixWord ++ tailWord_2240028) baseStart_2240028 baseEnd_2240028 := by
    simpa [prefixWord, tailWord_2240028, baseEnd_2240028] using wordTrace_append hprefix tailTrace_2240028
  have hstable : (prefixWord ++ tailWord_2240028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240028).length < 2 ^ (prefixWord ++ tailWord_2240028).sum := by decide
  have hdescent : baseEnd_2240028 < baseStart_2240028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240051 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 3, 3, 2]
def baseStart_2240051 : Nat := 118140960795 + 2240051 * 2 ^ 59
def prefixEnd_2240051 : Nat := 4983230072969 + 3 ^ 40 * 2240051 * 2
def baseEnd_2240051 : Nat := 1150222853584720523860699

theorem tailTrace_2240051 : CollatzResearch.WordTrace tailWord_2240051 prefixEnd_2240051 1150222853584720523860699 := by
  unfold tailWord_2240051
  simp only [CollatzResearch.WordTrace]
  refine ⟨81701372007685272097936007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54467581338456848065290671 81701372007685272097936007)
  ·
    refine ⟨122552058011527908146904011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81701372007685272097936007 122552058011527908146904011)
    ·
      refine ⟨183828087017291862220356017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122552058011527908146904011 183828087017291862220356017)
      ·
        refine ⟨137871065262968896665267013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183828087017291862220356017 137871065262968896665267013)
        ·
          refine ⟨25850824736806668124737565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137871065262968896665267013 25850824736806668124737565)
          ·
            refine ⟨9694059276302500546776587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25850824736806668124737565 9694059276302500546776587)
            ·
              refine ⟨14541088914453750820164881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9694059276302500546776587 14541088914453750820164881)
              ·
                refine ⟨10905816685840313115123661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14541088914453750820164881 10905816685840313115123661)
                ·
                  refine ⟨4089681257190117418171373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10905816685840313115123661 4089681257190117418171373)
                  ·
                    refine ⟨1533630471446294031814265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4089681257190117418171373 1533630471446294031814265)
                    ·
                      refine ⟨1150222853584720523860699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533630471446294031814265 1150222853584720523860699)
                      ·
                        rfl

theorem cell23_2240051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3, 2].length) (baseStart_2240051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240051 prefixEnd_2240051 := by exact prefixLift 2240051
  have htrace : WordTrace (prefixWord ++ tailWord_2240051) baseStart_2240051 baseEnd_2240051 := by
    simpa [prefixWord, tailWord_2240051, baseEnd_2240051] using wordTrace_append hprefix tailTrace_2240051
  have hstable : (prefixWord ++ tailWord_2240051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240051).length < 2 ^ (prefixWord ++ tailWord_2240051).sum := by decide
  have hdescent : baseEnd_2240051 < baseStart_2240051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240081 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 1, 4, 2]
def baseStart_2240081 : Nat := 118140960795 + 2240081 * 2 ^ 59
def prefixEnd_2240081 : Nat := 4983230072969 + 3 ^ 40 * 2240081 * 2
def baseEnd_2240081 : Nat := 1150238258004355406485561

theorem tailTrace_2240081 : CollatzResearch.WordTrace tailWord_2240081 prefixEnd_2240081 1150238258004355406485561 := by
  unfold tailWord_2240081
  simp only [CollatzResearch.WordTrace]
  refine ⟨81702466197576587221528097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54468310798384391481018731 81702466197576587221528097)
  ·
    refine ⟨61276849648182440416146073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81702466197576587221528097 61276849648182440416146073)
    ·
      refine ⟨45957637236136830312109555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61276849648182440416146073 45957637236136830312109555)
      ·
        refine ⟨68936455854205245468164333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45957637236136830312109555 68936455854205245468164333)
        ·
          refine ⟨25851170945326967050561625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68936455854205245468164333 25851170945326967050561625)
          ·
            refine ⟨19388378208995225287921219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25851170945326967050561625 19388378208995225287921219)
            ·
              refine ⟨29082567313492837931881829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19388378208995225287921219 29082567313492837931881829)
              ·
                refine ⟨5452981371279907112227843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29082567313492837931881829 5452981371279907112227843)
                ·
                  refine ⟨8179472056919860668341765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5452981371279907112227843 8179472056919860668341765)
                  ·
                    refine ⟨1533651010672473875314081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8179472056919860668341765 1533651010672473875314081)
                    ·
                      refine ⟨1150238258004355406485561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533651010672473875314081 1150238258004355406485561)
                      ·
                        rfl

theorem cell23_2240081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_2240081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240081 prefixEnd_2240081 := by exact prefixLift 2240081
  have htrace : WordTrace (prefixWord ++ tailWord_2240081) baseStart_2240081 baseEnd_2240081 := by
    simpa [prefixWord, tailWord_2240081, baseEnd_2240081] using wordTrace_append hprefix tailTrace_2240081
  have hstable : (prefixWord ++ tailWord_2240081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240081).length < 2 ^ (prefixWord ++ tailWord_2240081).sum := by decide
  have hdescent : baseEnd_2240081 < baseStart_2240081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240084 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2240084 : Nat := 118140960795 + 2240084 * 2 ^ 59
def prefixEnd_2240084 : Nat := 4983230072969 + 3 ^ 40 * 2240084 * 2
def baseEnd_2240084 : Nat := 1150239798446318894748047

theorem tailTrace_2240084 : CollatzResearch.WordTrace tailWord_2240084 prefixEnd_2240084 1150239798446318894748047 := by
  unfold tailWord_2240084
  simp only [CollatzResearch.WordTrace]
  refine ⟨40851287808282859366943653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54468383744377145822591537 40851287808282859366943653)
  ·
    refine ⟨7659616464053036131301935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40851287808282859366943653 7659616464053036131301935)
    ·
      refine ⟨11489424696079554196952903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7659616464053036131301935 11489424696079554196952903)
      ·
        refine ⟨17234137044119331295429355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11489424696079554196952903 17234137044119331295429355)
        ·
          refine ⟨25851205566178996943144033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17234137044119331295429355 25851205566178996943144033)
          ·
            refine ⟨19388404174634247707358025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25851205566178996943144033 19388404174634247707358025)
            ·
              refine ⟨14541303130975685780518519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19388404174634247707358025 14541303130975685780518519)
              ·
                refine ⟨21811954696463528670777779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14541303130975685780518519 21811954696463528670777779)
                ·
                  refine ⟨32717932044695293006166669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21811954696463528670777779 32717932044695293006166669)
                  ·
                    refine ⟨12269224516760734877312501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32717932044695293006166669 12269224516760734877312501)
                    ·
                      refine ⟨1150239798446318894748047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12269224516760734877312501 1150239798446318894748047)
                      ·
                        rfl

theorem cell23_2240084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2240084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240084 prefixEnd_2240084 := by exact prefixLift 2240084
  have htrace : WordTrace (prefixWord ++ tailWord_2240084) baseStart_2240084 baseEnd_2240084 := by
    simpa [prefixWord, tailWord_2240084, baseEnd_2240084] using wordTrace_append hprefix tailTrace_2240084
  have hstable : (prefixWord ++ tailWord_2240084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240084).length < 2 ^ (prefixWord ++ tailWord_2240084).sum := by decide
  have hdescent : baseEnd_2240084 < baseStart_2240084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240138 : List Nat := [3, 1, 2, 3, 2, 1, 3, 3, 5]
def baseStart_2240138 : Nat := 118140960795 + 2240138 * 2 ^ 59
def prefixEnd_2240138 : Nat := 4983230072969 + 3 ^ 40 * 2240138 * 2
def baseEnd_2240138 : Nat := 127807502933517964830311

theorem tailTrace_2240138 : CollatzResearch.WordTrace tailWord_2240138 prefixEnd_2240138 127807502933517964830311 := by
  unfold tailWord_2240138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20426136289592521489088267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54469696772246723970902045 20426136289592521489088267)
  ·
    refine ⟨30639204434388782233632401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20426136289592521489088267 30639204434388782233632401)
    ·
      refine ⟨22979403325791586675224301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30639204434388782233632401 22979403325791586675224301)
      ·
        refine ⟨8617276247171845003209113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22979403325791586675224301 8617276247171845003209113)
        ·
          refine ⟨6462957185378883752406835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8617276247171845003209113 6462957185378883752406835)
          ·
            refine ⟨9694435778068325628610253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6462957185378883752406835 9694435778068325628610253)
            ·
              refine ⟨3635413416775622110728845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9694435778068325628610253 3635413416775622110728845)
              ·
                refine ⟨1363280031290858291523317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3635413416775622110728845 1363280031290858291523317)
                ·
                  refine ⟨127807502933517964830311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1363280031290858291523317 127807502933517964830311)
                  ·
                    rfl

theorem cell23_2240138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_2240138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240138 prefixEnd_2240138 := by exact prefixLift 2240138
  have htrace : WordTrace (prefixWord ++ tailWord_2240138) baseStart_2240138 baseEnd_2240138 := by
    simpa [prefixWord, tailWord_2240138, baseEnd_2240138] using wordTrace_append hprefix tailTrace_2240138
  have hstable : (prefixWord ++ tailWord_2240138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240138).length < 2 ^ (prefixWord ++ tailWord_2240138).sum := by decide
  have hdescent : baseEnd_2240138 < baseStart_2240138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240151 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 2, 5]
def baseStart_2240151 : Nat := 118140960795 + 2240151 * 2 ^ 59
def prefixEnd_2240151 : Nat := 4983230072969 + 3 ^ 40 * 2240151 * 2
def baseEnd_2240151 : Nat := 383424733883390044203413

theorem tailTrace_2240151 : CollatzResearch.WordTrace tailWord_2240151 prefixEnd_2240151 383424733883390044203413 := by
  unfold tailWord_2240151
  simp only [CollatzResearch.WordTrace]
  refine ⟨81705019307322989176576307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54470012871548659451050871 81705019307322989176576307)
  ·
    refine ⟨122557528960984483764864461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81705019307322989176576307 122557528960984483764864461)
    ·
      refine ⟨45959073360369181411824173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122557528960984483764864461 45959073360369181411824173)
      ·
        refine ⟨17234652510138443029434065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45959073360369181411824173 17234652510138443029434065)
        ·
          refine ⟨12925989382603832272075549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17234652510138443029434065 12925989382603832272075549)
          ·
            refine ⟨4847246018476437102028331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12925989382603832272075549 4847246018476437102028331)
            ·
              refine ⟨7270869027714655653042497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847246018476437102028331 7270869027714655653042497)
              ·
                refine ⟨5453151770785991739781873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7270869027714655653042497 5453151770785991739781873)
                ·
                  refine ⟨4089863828089493804836405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5453151770785991739781873 4089863828089493804836405)
                  ·
                    refine ⟨383424733883390044203413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4089863828089493804836405 383424733883390044203413)
                    ·
                      rfl

theorem cell23_2240151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_2240151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240151 prefixEnd_2240151 := by exact prefixLift 2240151
  have htrace : WordTrace (prefixWord ++ tailWord_2240151) baseStart_2240151 baseEnd_2240151 := by
    simpa [prefixWord, tailWord_2240151, baseEnd_2240151] using wordTrace_append hprefix tailTrace_2240151
  have hstable : (prefixWord ++ tailWord_2240151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240151).length < 2 ^ (prefixWord ++ tailWord_2240151).sum := by decide
  have hdescent : baseEnd_2240151 < baseStart_2240151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240161 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2240161 : Nat := 118140960795 + 2240161 * 2 ^ 59
def prefixEnd_2240161 : Nat := 4983230072969 + 3 ^ 40 * 2240161 * 2
def baseEnd_2240161 : Nat := 1150279336456715093485193

theorem tailTrace_2240161 : CollatzResearch.WordTrace tailWord_2240161 prefixEnd_2240161 1150279336456715093485193 := by
  unfold tailWord_2240161
  simp only [CollatzResearch.WordTrace]
  refine ⟨81705384037286760884440337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54470256024857840589626891 81705384037286760884440337)
  ·
    refine ⟨61279038027965070663330253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81705384037286760884440337 61279038027965070663330253)
    ·
      refine ⟨22979639260486901498748845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61279038027965070663330253 22979639260486901498748845)
      ·
        refine ⟨8617364722682588062030817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22979639260486901498748845 8617364722682588062030817)
        ·
          refine ⟨6463023542011941046523113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8617364722682588062030817 6463023542011941046523113)
          ·
            refine ⟨4847267656508955784892335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6463023542011941046523113 4847267656508955784892335)
            ·
              refine ⟨7270901484763433677338503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847267656508955784892335 7270901484763433677338503)
              ·
                refine ⟨10906352227145150516007755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270901484763433677338503 10906352227145150516007755)
                ·
                  refine ⟨16359528340717725774011633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10906352227145150516007755 16359528340717725774011633)
                  ·
                    refine ⟨12269646255538294330508725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16359528340717725774011633 12269646255538294330508725)
                    ·
                      refine ⟨1150279336456715093485193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12269646255538294330508725 1150279336456715093485193)
                      ·
                        rfl

theorem cell23_2240161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2240161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240161 prefixEnd_2240161 := by exact prefixLift 2240161
  have htrace : WordTrace (prefixWord ++ tailWord_2240161) baseStart_2240161 baseEnd_2240161 := by
    simpa [prefixWord, tailWord_2240161, baseEnd_2240161] using wordTrace_append hprefix tailTrace_2240161
  have hstable : (prefixWord ++ tailWord_2240161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240161).length < 2 ^ (prefixWord ++ tailWord_2240161).sum := by decide
  have hdescent : baseEnd_2240161 < baseStart_2240161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240184 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_2240184 : Nat := 118140960795 + 2240184 * 2 ^ 59
def prefixEnd_2240184 : Nat := 4983230072969 + 3 ^ 40 * 2240184 * 2
def baseEnd_2240184 : Nat := 1150291146511768503497587

theorem tailTrace_2240184 : CollatzResearch.WordTrace tailWord_2240184 prefixEnd_2240184 1150291146511768503497587 := by
  unfold tailWord_2240184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40853111458101717906263803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54470815277468957208351737 40853111458101717906263803)
  ·
    refine ⟨61279667187152576859395705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40853111458101717906263803 61279667187152576859395705)
    ·
      refine ⟨45959750390364432644546779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61279667187152576859395705 45959750390364432644546779)
      ·
        refine ⟨68939625585546648966820169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45959750390364432644546779 68939625585546648966820169)
        ·
          refine ⟨51704719189159986725115127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68939625585546648966820169 51704719189159986725115127)
          ·
            refine ⟨77557078783739980087672691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51704719189159986725115127 77557078783739980087672691)
            ·
              refine ⟨116335618175609970131509037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77557078783739980087672691 116335618175609970131509037)
              ·
                refine ⟨43625856815853738799315889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116335618175609970131509037 43625856815853738799315889)
                ·
                  refine ⟨32719392611890304099486917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43625856815853738799315889 32719392611890304099486917)
                  ·
                    refine ⟨6134886114729432018653797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32719392611890304099486917 6134886114729432018653797)
                    ·
                      refine ⟨1150291146511768503497587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6134886114729432018653797 1150291146511768503497587)
                      ·
                        rfl

theorem cell23_2240184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_2240184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240184 prefixEnd_2240184 := by exact prefixLift 2240184
  have htrace : WordTrace (prefixWord ++ tailWord_2240184) baseStart_2240184 baseEnd_2240184 := by
    simpa [prefixWord, tailWord_2240184, baseEnd_2240184] using wordTrace_append hprefix tailTrace_2240184
  have hstable : (prefixWord ++ tailWord_2240184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240184).length < 2 ^ (prefixWord ++ tailWord_2240184).sum := by decide
  have hdescent : baseEnd_2240184 < baseStart_2240184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240188 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_2240188 : Nat := 118140960795 + 2240188 * 2 ^ 59
def prefixEnd_2240188 : Nat := 4983230072969 + 3 ^ 40 * 2240188 * 2
def baseEnd_2240188 : Nat := 1150293200434386487847569

theorem tailTrace_2240188 : CollatzResearch.WordTrace tailWord_2240188 prefixEnd_2240188 1150293200434386487847569 := by
  unfold tailWord_2240188
  simp only [CollatzResearch.WordTrace]
  refine ⟨40853184404094472247836609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54470912538792629663782145 40853184404094472247836609)
  ·
    refine ⟨30639888303070854185877457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40853184404094472247836609 30639888303070854185877457)
    ·
      refine ⟨22979916227303140639408093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30639888303070854185877457 22979916227303140639408093)
      ·
        refine ⟨8617468585238677739778035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22979916227303140639408093 8617468585238677739778035)
        ·
          refine ⟨12926202877858016609667053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8617468585238677739778035 12926202877858016609667053)
          ·
            refine ⟨4847326079196756228625145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12926202877858016609667053 4847326079196756228625145)
            ·
              refine ⟨3635494559397567171468859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4847326079196756228625145 3635494559397567171468859)
              ·
                refine ⟨5453241839096350757203289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635494559397567171468859 5453241839096350757203289)
                ·
                  refine ⟨4089931379322263067902467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5453241839096350757203289 4089931379322263067902467)
                  ·
                    refine ⟨6134897068983394601853701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4089931379322263067902467 6134897068983394601853701)
                    ·
                      refine ⟨1150293200434386487847569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6134897068983394601853701 1150293200434386487847569)
                      ·
                        rfl

theorem cell23_2240188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_2240188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240188 prefixEnd_2240188 := by exact prefixLift 2240188
  have htrace : WordTrace (prefixWord ++ tailWord_2240188) baseStart_2240188 baseEnd_2240188 := by
    simpa [prefixWord, tailWord_2240188, baseEnd_2240188] using wordTrace_append hprefix tailTrace_2240188
  have hstable : (prefixWord ++ tailWord_2240188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240188).length < 2 ^ (prefixWord ++ tailWord_2240188).sum := by decide
  have hdescent : baseEnd_2240188 < baseStart_2240188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240205 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2240205 : Nat := 118140960795 + 2240205 * 2 ^ 59
def prefixEnd_2240205 : Nat := 4983230072969 + 3 ^ 40 * 2240205 * 2
def baseEnd_2240205 : Nat := 1150301929605512921334991

theorem tailTrace_2240205 : CollatzResearch.WordTrace tailWord_2240205 prefixEnd_2240205 1150301929605512921334991 := by
  unfold tailWord_2240205
  simp only [CollatzResearch.WordTrace]
  refine ⟨81706988849127356399042069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54471325899418237599361379 81706988849127356399042069)
  ·
    refine ⟨3830015102302844831205097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81706988849127356399042069 3830015102302844831205097)
    ·
      refine ⟨2872511326727133623403823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3830015102302844831205097 2872511326727133623403823)
      ·
        refine ⟨4308766990090700435105735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872511326727133623403823 4308766990090700435105735)
        ·
          refine ⟨6463150485136050652658603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4308766990090700435105735 6463150485136050652658603)
          ·
            refine ⟨9694725727704075978987905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6463150485136050652658603 9694725727704075978987905)
            ·
              refine ⟨7271044295778056984240929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9694725727704075978987905 7271044295778056984240929)
              ·
                refine ⟨5453283221833542738180697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7271044295778056984240929 5453283221833542738180697)
                ·
                  refine ⟨4089962416375157053635523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5453283221833542738180697 4089962416375157053635523)
                  ·
                    refine ⟨6134943624562735580453285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4089962416375157053635523 6134943624562735580453285)
                    ·
                      refine ⟨1150301929605512921334991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6134943624562735580453285 1150301929605512921334991)
                      ·
                        rfl

theorem cell23_2240205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2240205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240205 prefixEnd_2240205 := by exact prefixLift 2240205
  have htrace : WordTrace (prefixWord ++ tailWord_2240205) baseStart_2240205 baseEnd_2240205 := by
    simpa [prefixWord, tailWord_2240205, baseEnd_2240205] using wordTrace_append hprefix tailTrace_2240205
  have hstable : (prefixWord ++ tailWord_2240205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240205).length < 2 ^ (prefixWord ++ tailWord_2240205).sum := by decide
  have hdescent : baseEnd_2240205 < baseStart_2240205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240241 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 3, 5]
def baseStart_2240241 : Nat := 118140960795 + 2240241 * 2 ^ 59
def prefixEnd_2240241 : Nat := 4983230072969 + 3 ^ 40 * 2240241 * 2
def baseEnd_2240241 : Nat := 383440138303024926828275

theorem tailTrace_2240241 : CollatzResearch.WordTrace tailWord_2240241 prefixEnd_2240241 383440138303024926828275 := by
  unfold tailWord_2240241
  simp only [CollatzResearch.WordTrace]
  refine ⟨81708301876996934547352577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54472201251331289698235051 81708301876996934547352577)
  ·
    refine ⟨61281226407747700910514433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81708301876996934547352577 61281226407747700910514433)
    ·
      refine ⟨45960919805810775682885825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61281226407747700910514433 45960919805810775682885825)
      ·
        refine ⟨34470689854358081762164369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45960919805810775682885825 34470689854358081762164369)
        ·
          refine ⟨25853017390768561321623277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34470689854358081762164369 25853017390768561321623277)
          ·
            refine ⟨9694881521538210495608729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25853017390768561321623277 9694881521538210495608729)
            ·
              refine ⟨7271161141153657871706547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9694881521538210495608729 7271161141153657871706547)
              ·
                refine ⟨10906741711730486807559821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7271161141153657871706547 10906741711730486807559821)
                ·
                  refine ⟨4090028141898932552834933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10906741711730486807559821 4090028141898932552834933)
                  ·
                    refine ⟨383440138303024926828275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4090028141898932552834933 383440138303024926828275)
                    ·
                      rfl

theorem cell23_2240241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_2240241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240241 prefixEnd_2240241 := by exact prefixLift 2240241
  have htrace : WordTrace (prefixWord ++ tailWord_2240241) baseStart_2240241 baseEnd_2240241 := by
    simpa [prefixWord, tailWord_2240241, baseEnd_2240241] using wordTrace_append hprefix tailTrace_2240241
  have hstable : (prefixWord ++ tailWord_2240241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240241).length < 2 ^ (prefixWord ++ tailWord_2240241).sum := by decide
  have hdescent : baseEnd_2240241 < baseStart_2240241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240248 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 2, 3, 2]
def baseStart_2240248 : Nat := 118140960795 + 2240248 * 2 ^ 59
def prefixEnd_2240248 : Nat := 4983230072969 + 3 ^ 40 * 2240248 * 2
def baseEnd_2240248 : Nat := 1150324009273656253097293

theorem tailTrace_2240248 : CollatzResearch.WordTrace tailWord_2240248 prefixEnd_2240248 1150324009273656253097293 := by
  unfold tailWord_2240248
  simp only [CollatzResearch.WordTrace]
  refine ⟨40854278593985787371428699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54472371458647716495238265 40854278593985787371428699)
  ·
    refine ⟨61281417890978681057143049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40854278593985787371428699 61281417890978681057143049)
    ·
      refine ⟨45961063418234010792857287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61281417890978681057143049 45961063418234010792857287)
      ·
        refine ⟨68941595127351016189285931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45961063418234010792857287 68941595127351016189285931)
        ·
          refine ⟨103412392691026524283928897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68941595127351016189285931 103412392691026524283928897)
          ·
            refine ⟨77559294518269893212946673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103412392691026524283928897 77559294518269893212946673)
            ·
              refine ⟨58169470888702419909710005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77559294518269893212946673 58169470888702419909710005)
              ·
                refine ⟨5453387895815851866535313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58169470888702419909710005 5453387895815851866535313)
                ·
                  refine ⟨4090040921861888899901485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5453387895815851866535313 4090040921861888899901485)
                  ·
                    refine ⟨1533765345698208337463057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4090040921861888899901485 1533765345698208337463057)
                    ·
                      refine ⟨1150324009273656253097293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533765345698208337463057 1150324009273656253097293)
                      ·
                        rfl

theorem cell23_2240248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_2240248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240248 prefixEnd_2240248 := by exact prefixLift 2240248
  have htrace : WordTrace (prefixWord ++ tailWord_2240248) baseStart_2240248 baseEnd_2240248 := by
    simpa [prefixWord, tailWord_2240248, baseEnd_2240248] using wordTrace_append hprefix tailTrace_2240248
  have hstable : (prefixWord ++ tailWord_2240248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240248).length < 2 ^ (prefixWord ++ tailWord_2240248).sum := by decide
  have hdescent : baseEnd_2240248 < baseStart_2240248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240255 : List Nat := [1, 1, 2, 2, 1, 3, 3, 5, 1, 1, 3]
def baseStart_2240255 : Nat := 118140960795 + 2240255 * 2 ^ 59
def prefixEnd_2240255 : Nat := 4983230072969 + 3 ^ 40 * 2240255 * 2
def baseEnd_2240255 : Nat := 1150327603638237725709761

theorem tailTrace_2240255 : CollatzResearch.WordTrace tailWord_2240255 prefixEnd_2240255 1150327603638237725709761 := by
  unfold tailWord_2240255
  simp only [CollatzResearch.WordTrace]
  refine ⟨81708812498946214938362219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54472541665964143292241479 81708812498946214938362219)
  ·
    refine ⟨122563218748419322407543329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81708812498946214938362219 122563218748419322407543329)
    ·
      refine ⟨91922414061314491805657497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122563218748419322407543329 91922414061314491805657497)
      ·
        refine ⟨68941810545985868854243123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91922414061314491805657497 68941810545985868854243123)
        ·
          refine ⟨103412715818978803281364685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68941810545985868854243123 103412715818978803281364685)
          ·
            refine ⟨38779768432117051230511757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103412715818978803281364685 38779768432117051230511757)
            ·
              refine ⟨14542413162043894211441909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38779768432117051230511757 14542413162043894211441909)
              ·
                refine ⟨1363351233941615082322679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14542413162043894211441909 1363351233941615082322679)
                ·
                  refine ⟨2045026850912422623484019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363351233941615082322679 2045026850912422623484019)
                  ·
                    refine ⟨3067540276368633935226029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045026850912422623484019 3067540276368633935226029)
                    ·
                      refine ⟨1150327603638237725709761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067540276368633935226029 1150327603638237725709761)
                      ·
                        rfl

theorem cell23_2240255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_2240255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240255 prefixEnd_2240255 := by exact prefixLift 2240255
  have htrace : WordTrace (prefixWord ++ tailWord_2240255) baseStart_2240255 baseEnd_2240255 := by
    simpa [prefixWord, tailWord_2240255, baseEnd_2240255] using wordTrace_append hprefix tailTrace_2240255
  have hstable : (prefixWord ++ tailWord_2240255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240255).length < 2 ^ (prefixWord ++ tailWord_2240255).sum := by decide
  have hdescent : baseEnd_2240255 < baseStart_2240255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240318 : List Nat := [4, 2, 1, 2, 2, 3, 9]
def baseStart_2240318 : Nat := 118140960795 + 2240318 * 2 ^ 59
def prefixEnd_2240318 : Nat := 4983230072969 + 3 ^ 40 * 2240318 * 2
def baseEnd_2240318 : Nat := 14201974727400876286691

theorem tailTrace_2240318 : CollatzResearch.WordTrace tailWord_2240318 prefixEnd_2240318 14201974727400876286691 := by
  unfold tailWord_2240318
  simp only [CollatzResearch.WordTrace]
  refine ⟨10213888787214747087238201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54474073531811984465270405 10213888787214747087238201)
  ·
    refine ⟨7660416590411060315428651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10213888787214747087238201 7660416590411060315428651)
    ·
      refine ⟨11490624885616590473142977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7660416590411060315428651 11490624885616590473142977)
      ·
        refine ⟨8617968664212442854857233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11490624885616590473142977 8617968664212442854857233)
        ·
          refine ⟨6463476498159332141142925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8617968664212442854857233 6463476498159332141142925)
          ·
            refine ⟨2423803686809749552928597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6463476498159332141142925 2423803686809749552928597)
            ·
              refine ⟨14201974727400876286691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2423803686809749552928597 14201974727400876286691)
              ·
                rfl

theorem cell23_2240318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 9].length) (baseStart_2240318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240318 prefixEnd_2240318 := by exact prefixLift 2240318
  have htrace : WordTrace (prefixWord ++ tailWord_2240318) baseStart_2240318 baseEnd_2240318 := by
    simpa [prefixWord, tailWord_2240318, baseEnd_2240318] using wordTrace_append hprefix tailTrace_2240318
  have hstable : (prefixWord ++ tailWord_2240318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240318).length < 2 ^ (prefixWord ++ tailWord_2240318).sum := by decide
  have hdescent : baseEnd_2240318 < baseStart_2240318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240329 : List Nat := [1, 2, 1, 1, 2, 4, 5, 2, 1, 2, 2]
def baseStart_2240329 : Nat := 118140960795 + 2240329 * 2 ^ 59
def prefixEnd_2240329 : Nat := 4983230072969 + 3 ^ 40 * 2240329 * 2
def baseEnd_2240329 : Nat := 1150365601206670436184421

theorem tailTrace_2240329 : CollatzResearch.WordTrace tailWord_2240329 prefixEnd_2240329 1150365601206670436184421 := by
  unfold tailWord_2240329
  simp only [CollatzResearch.WordTrace]
  refine ⟨81711511500678125576556041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54474341000452083717704027 81711511500678125576556041)
  ·
    refine ⟨61283633625508594182417031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81711511500678125576556041 61283633625508594182417031)
    ·
      refine ⟨91925450438262891273625547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61283633625508594182417031 91925450438262891273625547)
      ·
        refine ⟨137888175657394336910438321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91925450438262891273625547 137888175657394336910438321)
        ·
          refine ⟨103416131743045752682828741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137888175657394336910438321 103416131743045752682828741)
          ·
            refine ⟨19390524701821078628030389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103416131743045752682828741 19390524701821078628030389)
            ·
              refine ⟨1817861690795726121377849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19390524701821078628030389 1817861690795726121377849)
              ·
                refine ⟨1363396268096794591033387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817861690795726121377849 1363396268096794591033387)
                ·
                  refine ⟨2045094402145191886550081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363396268096794591033387 2045094402145191886550081)
                  ·
                    refine ⟨1533820801608893914912561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2045094402145191886550081 1533820801608893914912561)
                    ·
                      refine ⟨1150365601206670436184421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533820801608893914912561 1150365601206670436184421)
                      ·
                        rfl

theorem cell23_2240329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 2, 2].length) (baseStart_2240329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240329 prefixEnd_2240329 := by exact prefixLift 2240329
  have htrace : WordTrace (prefixWord ++ tailWord_2240329) baseStart_2240329 baseEnd_2240329 := by
    simpa [prefixWord, tailWord_2240329, baseEnd_2240329] using wordTrace_append hprefix tailTrace_2240329
  have hstable : (prefixWord ++ tailWord_2240329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240329).length < 2 ^ (prefixWord ++ tailWord_2240329).sum := by decide
  have hdescent : baseEnd_2240329 < baseStart_2240329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240345 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 3]
def baseStart_2240345 : Nat := 118140960795 + 2240345 * 2 ^ 59
def prefixEnd_2240345 : Nat := 4983230072969 + 3 ^ 40 * 2240345 * 2
def baseEnd_2240345 : Nat := 1150373816897142373584347

theorem tailTrace_2240345 : CollatzResearch.WordTrace tailWord_2240345 prefixEnd_2240345 1150373816897142373584347 := by
  unfold tailWord_2240345
  simp only [CollatzResearch.WordTrace]
  refine ⟨81712095068620160309138489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54474730045746773539425659 81712095068620160309138489)
  ·
    refine ⟨61284071301465120231853867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81712095068620160309138489 61284071301465120231853867)
    ·
      refine ⟨91926106952197680347780801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61284071301465120231853867 91926106952197680347780801)
      ·
        refine ⟨68944580214148260260835601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91926106952197680347780801 68944580214148260260835601)
        ·
          refine ⟨51708435160611195195626701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68944580214148260260835601 51708435160611195195626701)
          ·
            refine ⟨19390663185229198198360013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51708435160611195195626701 19390663185229198198360013)
            ·
              refine ⟨7271498694460949324385005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19390663185229198198360013 7271498694460949324385005)
              ·
                refine ⟨2726812010422855996644377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7271498694460949324385005 2726812010422855996644377)
                ·
                  refine ⟨2045109007817141997483283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2726812010422855996644377 2045109007817141997483283)
                  ·
                    refine ⟨3067663511725712996224925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045109007817141997483283 3067663511725712996224925)
                    ·
                      refine ⟨1150373816897142373584347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067663511725712996224925 1150373816897142373584347)
                      ·
                        rfl

theorem cell23_2240345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_2240345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240345 prefixEnd_2240345 := by exact prefixLift 2240345
  have htrace : WordTrace (prefixWord ++ tailWord_2240345) baseStart_2240345 baseEnd_2240345 := by
    simpa [prefixWord, tailWord_2240345, baseEnd_2240345] using wordTrace_append hprefix tailTrace_2240345
  have hstable : (prefixWord ++ tailWord_2240345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240345).length < 2 ^ (prefixWord ++ tailWord_2240345).sum := by decide
  have hdescent : baseEnd_2240345 < baseStart_2240345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
